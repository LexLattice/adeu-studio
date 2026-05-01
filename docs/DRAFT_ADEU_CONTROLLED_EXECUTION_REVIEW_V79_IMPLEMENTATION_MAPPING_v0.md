# Draft ADEU Controlled Execution Review V79 Implementation Mapping v0

Status: support / implementation mapping record for planned `V79`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V79` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v69.md`
- `docs/ARCHITECTURE_ADEU_CONTROLLED_EXECUTION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V79` should add controlled execution review and run-plan readiness records
without turning them into:

- command execution;
- actual tool invocation;
- worker assignment or dispatch execution;
- target mutation;
- accepted effects;
- observed telemetry or verified rollback created by `V79`;
- product authorization;
- external branch activation;
- PR creation, commit, merge, release, or released truth;
- relation settlement, claim truth, benchmark truth, or model selection;
- living-memory authority;
- recursive policy amendment.

The implementation target is a typed controlled-execution review family that
can represent:

- source-bound controlled-execution review requests;
- source indexes that distinguish eligibility sources from support context;
- non-execution guardrails;
- execution run plans without running them;
- tool-invocation plans without invoking tools;
- effect-monitoring contracts without observing effects;
- controlled-execution exceptions without resolving them by prose;
- review summaries and post-review handoffs without later-family completion.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded controlled execution review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus221/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V79` still describes repo/corpus review
metadata and authority posture. If a later family becomes live command
execution, tool invocation, worker dispatch, product UI, external automation,
release automation, or graph query runtime, that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/controlled_execution_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_controlled_execution_review_v79a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_controlled_execution_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_non_execution_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_execution_run_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_tool_invocation_plan.v1.json`
- `packages/adeu_repo_description/schema/repo_execution_effect_monitoring_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_controlled_execution_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_controlled_execution_review_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_controlled_execution_review_request.schema.json`
- `spec/repo_controlled_execution_source_index.schema.json`
- `spec/repo_controlled_execution_non_execution_guardrail.schema.json`
- `spec/repo_execution_run_plan.schema.json`
- `spec/repo_tool_invocation_plan.schema.json`
- `spec/repo_execution_effect_monitoring_contract.schema.json`
- `spec/repo_controlled_execution_exception_register.schema.json`
- `spec/repo_controlled_execution_review_summary.schema.json`
- `spec/repo_post_controlled_execution_review_handoff.schema.json`
- `spec/repo_controlled_execution_review_family_closeout_alignment.schema.json`

## 3. Candidate `V79` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_controlled_execution_review_request@1` | `V79-A` | request rows over released `V78-C` readiness / handoff substrate |
| `repo_controlled_execution_source_index@1` | `V79-A` | concrete source rows, absence posture, and source-role classification |
| `repo_controlled_execution_non_execution_guardrail@1` | `V79-A` | non-execution, non-invocation, non-dispatch, non-product, non-external, non-release, and non-policy guardrails |
| `repo_execution_run_plan@1` | `V79-B` | bounded run-plan posture without running commands |
| `repo_tool_invocation_plan@1` | `V79-B` | bounded tool-invocation plan without invoking tools |
| `repo_execution_effect_monitoring_contract@1` | `V79-B` | effect, telemetry, rollback, and operator-confirmation monitoring requirements |
| `repo_controlled_execution_exception_register@1` | `V79-B` | missing source, authority, scope, telemetry, rollback, product, external, and release blockers |
| `repo_controlled_execution_review_summary@1` | `V79-C` | synthesis of run-plan readiness without execution |
| `repo_post_controlled_execution_review_handoff@1` | `V79-C` | later-review handoff after controlled execution review |
| `repo_controlled_execution_review_family_closeout_alignment@1` | `V79-C` | family closeout alignment without command execution or tool invocation |

`V79-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement run plans, tool-invocation
plans, monitoring contracts, exception registers, summaries, handoffs, command
execution, tool invocation, product workbenching, external branch activation,
or release authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V78` runtime execution authority review family closeout:
  - `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v220/evidence_inputs/v78_family_closeout_alignment_v220.json`
  - `artifacts/agent_harness/v220/evidence_inputs/v78c_runtime_execution_authority_closeout_evidence_v220.json`
- `V78-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_authority_readiness_summary_v220_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus220/repo_pre_execution_authority_review_handoff_v220_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus220/repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json`
- `V78-B` decision / permission / scope / exception fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus219/repo_runtime_execution_authority_decision_v219_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus219/repo_tool_use_permission_envelope_v219_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus219/repo_command_scope_authorization_boundary_v219_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus219/repo_runtime_authority_exception_register_v219_reference.json`
- support lineage:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become controlled execution source rows.

If any expected source is missing when an active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct controlled execution state from planning prose.

## 5. Shared Row Vocabulary

Minimum controlled execution source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `controlled_execution_source_role`
- `source_horizon`
- `limitation_note`

Minimum controlled execution source role:

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

Rows with `combined_dogfood_context` or `support_process_context` may
contextualize `V79-A`; they cannot be the only sources for
`eligible_for_controlled_execution_review`.

Minimum controlled execution review request fields:

- `execution_review_request_ref`
- `candidate_ref`
- `source_refs`
- `v78_summary_refs`
- `v78_handoff_refs`
- `v78_closeout_refs`
- `requested_execution_review_horizon`
- `execution_review_posture`
- `requested_run_plan_horizon`
- `requested_tool_invocation_horizon`
- `required_effect_monitoring_posture`
- `required_telemetry_posture`
- `required_rollback_posture`
- `required_operator_confirmation_posture`
- `required_authority_refs`
- `target_boundary_refs`
- `guardrail_refs`
- `controlled_execution_action_posture`
- `execution_posture`
- `tool_invocation_posture`
- `odeu_lanes`
- `limitation_note`

Minimum execution review posture:

- `eligible_for_controlled_execution_review`
- `blocked_by_missing_source`
- `blocked_by_missing_authority`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_gap`
- `blocked_by_unbounded_target`
- `blocked_by_missing_effect_monitoring`
- `blocked_by_missing_telemetry`
- `blocked_by_missing_rollback`
- `future_family_only`
- `rejected_out_of_scope`

The starter slice deliberately uses requested horizons and required postures
for run-plan, tool-invocation, monitoring, telemetry, rollback, and operator
confirmation pressure. `V79-A` must not emit refs to `V79-B` surfaces that do
not exist yet.

Minimum controlled execution action posture:

- `no_controlled_execution_performed_by_v79`
- `controlled_execution_requires_later_family`
- `controlled_execution_forbidden_by_this_family`

Minimum non-execution guardrail fields:

- `guardrail_ref`
- `candidate_ref`
- `source_refs`
- `forbidden_execution_actions`
- `forbidden_downstream_authority`
- `guardrail_posture`
- `limitation_note`

## 6. Fixture Strategy

First `V79-A` reference fixture should include:

- one source-bound self-evidencing runtime pressure row eligible for controlled
  execution review only;
- one typed-adjudication product pressure row blocked by product authority or
  future-family-only;
- one support / dogfood source row marked context-only, not eligibility by
  itself;
- one non-execution guardrail row with non-empty forbidden execution actions
  and downstream authority lists;
- zero run plans, zero tool-invocation plans, zero command executions, zero
  tool invocations, zero observed effects, zero telemetry-success rows, zero
  rollback-verification rows, zero dispatch rows, zero product / external /
  release rows, and zero later-family selections.

Reject fixtures should cover:

- support-only eligibility;
- request without source refs;
- unknown `V78-C` handoff refs;
- `V78` decision treated as execution authorization;
- tool-use permission envelope treated as tool invocation;
- command-scope boundary treated as target mutation authority;
- product pressure marked execution-ready;
- external pressure marked execution-ready without `V43` posture;
- empty forbidden execution actions;
- command output treated as authority;
- local tool result treated as authority.

## 7. Gate Strategy

For initial docs-only family bundle review:

- no active starter lock yet;
- no Python implementation expected.

For the future `V79-A` active starter:

- use canonical starter trio:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS221.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS221.md`
  - `docs/ASSESSMENT_vNEXT_PLUS221_EDGES.md`
- run `make arc-start-check ARC=221` for docs-only starter;
- run `make check` before any Python implementation PR.

## 8. Open Review Questions

- `V79-B` may represent a complete run plan for review only. `V79-C` should
  be the first slice allowed to summarize whether that package is ready,
  warning-ready, blocked, deferred, future-family-only, or out of scope.
- Operator confirmation should be first-class in `V79-B` as a requirement /
  source-bound review object, not as operator authorization.
- Effect monitoring and telemetry should remain one
  `repo_execution_effect_monitoring_contract@1` surface in `V79-B`, with
  embedded or referenced telemetry, rollback, and operator-confirmation
  requirement rows.
- Later actual execution may be future-family pressure, but `V79-C` must not
  preselect `V80`. The next selector should decide based on emitted rows and
  blockers.
