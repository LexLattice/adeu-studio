# Draft ADEU Controlled Execution Review V79-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V79-A`.

Authority layer: support.

This note does not authorize implementation by itself. It specifies the likely
starter slice that a future `vNext+221` lock may select after the `V79`
family bundle is reviewed.

## Slice Intent

`V79-A` should create the starter schema / model / validator backbone for
controlled execution review intake:

- `repo_controlled_execution_review_request@1`
- `repo_controlled_execution_source_index@1`
- `repo_controlled_execution_non_execution_guardrail@1`

The slice consumes released `V78-C` readiness / handoff / closeout substrate
and admits controlled-execution review pressure without creating run plans,
tool-invocation plans, execution, tool invocation, dispatch, product
authorization, external branch activation, release, or later-family selection.

## Expected Files

Implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/controlled_execution_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Schema files:

- `packages/adeu_repo_description/schema/repo_controlled_execution_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_non_execution_guardrail.v1.json`

Schema mirrors:

- `spec/repo_controlled_execution_review_request.schema.json`
- `spec/repo_controlled_execution_source_index.schema.json`
- `spec/repo_controlled_execution_non_execution_guardrail.schema.json`

Tests:

- `packages/adeu_repo_description/tests/test_controlled_execution_review_v79a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Fixtures:

- `apps/api/fixtures/repo_description/vnext_plus221/repo_controlled_execution_review_request_v221_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus221/repo_controlled_execution_source_index_v221_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus221/repo_controlled_execution_non_execution_guardrail_v221_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus221/repo_controlled_execution_v221_reject_*.json`

## Source Basis

Required concrete source rows should cover:

- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_FAMILY_CLOSEOUT_v0.md`
- `artifacts/agent_harness/v220/evidence_inputs/v78_family_closeout_alignment_v220.json`
- `artifacts/agent_harness/v220/evidence_inputs/v78c_runtime_execution_authority_closeout_evidence_v220.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_authority_readiness_summary_v220_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_pre_execution_authority_review_handoff_v220_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json`

Support or roadmap sources may contextualize `V79-A`; they cannot be the only
eligibility sources for an `eligible_for_controlled_execution_review` row.

Minimum source roles:

- `v78_readiness_summary_source`
- `v78_pre_execution_authority_review_handoff_source`
- `v78_family_closeout_source`
- `v78_authority_decision_context`
- `v78_tool_permission_context`
- `v78_command_scope_context`
- `v78_exception_context`
- `combined_dogfood_context`
- `support_process_context`
- `absence_marker`

An `eligible_for_controlled_execution_review` row must cite either a
`v78_readiness_summary_source` row or a
`v78_pre_execution_authority_review_handoff_source` row. Context-only dogfood
and support rows may not be the only eligibility basis.

`V79-A` should represent later run-plan, tool-invocation, monitoring,
telemetry, rollback, and operator-confirmation pressure through requested
horizons and required postures, not through refs to `V79-B` surfaces that do
not exist yet.

Required starter request fields include:

- `requested_run_plan_horizon`
- `requested_tool_invocation_horizon`
- `required_effect_monitoring_posture`
- `required_telemetry_posture`
- `required_rollback_posture`
- `required_operator_confirmation_posture`
- `controlled_execution_action_posture`

Reference rows must carry:

- `controlled_execution_action_posture =
  no_controlled_execution_performed_by_v79`
- `execution_posture = no_execution_performed_by_v79`
- `tool_invocation_posture = no_tool_invocation_performed_by_v79`

## Validation Rules

Local shape validation should enforce:

- stable schema names;
- sorted refs and deterministic ids;
- no absolute filesystem paths unless an existing repo pattern explicitly
  permits them;
- non-empty source refs for each request row;
- source rows have explicit source presence posture;
- no free-text authority layers;
- non-empty guardrail forbidden-action lists.

Bundle validation should enforce:

- request rows reference known source rows;
- eligible requests reference released `V78-C` handoff or summary refs and a
  matching eligibility source role;
- support-only sources cannot make a request eligible;
- product pressure cannot be marked execution-ready;
- external pressure cannot be marked execution-ready without concrete external
  branch or `V43` posture;
- all request rows carry no-execution and no-tool-invocation posture;
- guardrail rows reference known candidates and source rows;
- run-plan, tool-invocation-plan, effect-monitoring, telemetry, rollback, and
  operator-confirmation refs are absent from `V79-A` request rows;
- no `V79-A` row contains run-plan, tool-invocation-plan, command execution,
  tool invocation, dispatch, PR, commit, merge, release, product authorization,
  external activation, benchmark truth, model selection, living-memory
  authority, recursive policy amendment, or `V80` selection fields.

## Reference Fixture Intent

The first reference fixture should include:

- one self-evidencing workflow candidate sourced from `V78-C`, eligible only
  for controlled execution review;
- one typed-adjudication product wedge candidate blocked by product authority
  or future-family-only;
- source rows for `V78-C` fixtures and family closeout evidence;
- context-only dogfood source rows;
- non-execution guardrails for both candidates.

The fixture should include zero run plans, tool-invocation plans, command
executions, tool invocations, observed effects, telemetry-success rows,
rollback-verification rows, worker assignments, dispatch executions, product
authorizations, external branch activations, PR / commit / merge / release
rows, benchmark truth rows, global model selection rows, living-memory rows,
recursive policy amendment rows, or `V80` selection rows.

## Mandatory Reject Fixtures

- request with no source refs;
- source row without concrete source or explicit absence posture;
- eligible request sourced only by support dogfood;
- unknown `V78-C` handoff ref;
- `V78` decision treated as execution authorization;
- `V78` tool-use permission envelope treated as tool invocation;
- command-scope boundary treated as target mutation authority;
- product pressure marked execution-ready;
- external pressure marked execution-ready without `V43` posture;
- empty forbidden execution actions;
- non-empty run-plan, tool-invocation-plan, effect-monitoring, telemetry,
  rollback, or operator-confirmation refs in a `V79-A` request row;
- row claiming command execution or tool invocation;
- row selecting `V79-B`, `V79-C`, `V80`, product review, external branch, or
  release authority.

## Non-Selection

`V79-A` does not select `V79-B`, `V79-C`, command execution, tool invocation,
run plans, tool-invocation plans, effect-monitoring contracts, exception
registers, summaries, handoffs, product authorization, external branch
activation, release, dispatch, living memory, or recursive policy amendment.
