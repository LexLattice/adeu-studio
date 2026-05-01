# Draft ADEU Runtime Execution Authority V78 Implementation Mapping v0

Status: support / implementation mapping record for planned `V78`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V78` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V78` should add runtime execution authority and tool-use permission envelope
records without turning them into:

- command execution;
- actual tool invocation;
- worker assignment or dispatch execution;
- product authorization;
- external branch activation;
- PR creation, commit, merge, release, or released truth;
- relation settlement, claim truth, benchmark truth, or model selection;
- living-memory authority;
- recursive policy amendment.

The implementation target is a typed runtime authority family that can
represent:

- source-bound runtime execution authority requests;
- source indexes that distinguish authority sources from support context;
- non-action guardrails;
- authority decisions without executing commands;
- tool-use permission envelopes without invoking tools;
- command-scope authorization boundaries without running commands;
- runtime authority exceptions without resolving them by prose;
- readiness summaries and pre-execution-review handoffs without later-family
  completion.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded runtime execution authority records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus218/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V78` still describes repo/corpus
metadata and authority posture. If a later family becomes live command
execution, tool invocation, worker dispatch, product UI, external automation,
release automation, or graph query runtime, that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/runtime_execution_authority.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_runtime_execution_authority_v78a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_runtime_execution_authority_request.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_authority_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_authority_non_action_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_runtime_execution_authority_decision.v1.json`
- `packages/adeu_repo_description/schema/repo_tool_use_permission_envelope.v1.json`
- `packages/adeu_repo_description/schema/repo_command_scope_authorization_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_authority_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_authority_readiness_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_pre_execution_authority_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_execution_authority_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_runtime_execution_authority_request.schema.json`
- `spec/repo_runtime_authority_source_index.schema.json`
- `spec/repo_runtime_authority_non_action_guardrail.schema.json`
- `spec/repo_runtime_execution_authority_decision.schema.json`
- `spec/repo_tool_use_permission_envelope.schema.json`
- `spec/repo_command_scope_authorization_boundary.schema.json`
- `spec/repo_runtime_authority_exception_register.schema.json`
- `spec/repo_runtime_authority_readiness_summary.schema.json`
- `spec/repo_pre_execution_authority_review_handoff.schema.json`
- `spec/repo_runtime_execution_authority_family_closeout_alignment.schema.json`

## 3. Candidate `V78` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_runtime_execution_authority_request@1` | `V78-A` | request rows over released `V77-C` handoff and authority substrate |
| `repo_runtime_authority_source_index@1` | `V78-A` | concrete authority source rows, absence posture, and source-role classification |
| `repo_runtime_authority_non_action_guardrail@1` | `V78-A` | non-execution, non-tool-invocation, non-product, non-external, non-release, and non-policy guardrails |
| `repo_runtime_execution_authority_decision@1` | `V78-B` | bounded authority grant / deny / defer / block / reject decisions for later execution review |
| `repo_tool_use_permission_envelope@1` | `V78-B` | bounded tool-use permission posture without tool invocation |
| `repo_command_scope_authorization_boundary@1` | `V78-B` | command-intent, target, telemetry, rollback, and authority scope boundaries |
| `repo_runtime_authority_exception_register@1` | `V78-B` | missing source, authority, scope, telemetry, rollback, product, external, and release blockers |
| `repo_runtime_authority_readiness_summary@1` | `V78-C` | synthesis of authority and scope posture without execution |
| `repo_pre_execution_authority_review_handoff@1` | `V78-C` | later-review handoff after runtime authority review |
| `repo_runtime_execution_authority_family_closeout_alignment@1` | `V78-C` | family closeout alignment without command execution or release |

`V78-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement authority decisions,
tool-use permission envelopes, command-scope authorization boundaries,
exception registers, readiness summaries, handoffs, command execution, product
workbenching, external branch activation, or release authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V77` runtime-permission review family closeout:
  - `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v217/evidence_inputs/v77_family_closeout_alignment_v217.json`
  - `artifacts/agent_harness/v217/evidence_inputs/v77c_runtime_permission_closeout_evidence_v217.json`
- `V77-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_authority_posture_v217_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_review_summary_v217_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus217/repo_post_runtime_permission_review_handoff_v217_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_family_closeout_alignment_v217_reference.json`
- `V77-B` scope / evidence / rollback requirement fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus216/repo_command_preflight_contract_v216_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus216/repo_action_effect_envelope_v216_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus216/repo_runtime_telemetry_requirement_v216_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus216/repo_runtime_rollback_contract_v216_reference.json`
- support lineage:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become runtime authority source rows.

If any expected source is missing when an active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct runtime authority state from planning prose.

## 5. Shared Row Vocabulary

Minimum runtime authority source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `runtime_authority_source_role`
- `source_horizon`
- `limitation_note`

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

Starter reference rows should use `no_execution_performed_by_v78`.

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

Starter reference rows should use `no_tool_invocation_performed_by_v78`.

## 6. Validation Themes

Expected validators should enforce:

- source rows are explicit and concrete, or carry explicit absence posture;
- support context may contextualize `V78` but cannot be the only eligibility
  source for `eligible_for_runtime_execution_authority_review`;
- runtime authority requests reference released `V77-C` authority, summary,
  handoff, or closeout rows, or explicit absence rows;
- product and external branch pressure remains blocked or future-family-only
  unless the row is explicitly routed as future product / external review;
- command preflight is not command execution;
- tool-use permission envelope is not tool invocation;
- command-scope boundary is not permission to mutate target state in `V78`;
- telemetry and rollback requirements must be source-bound;
- authority grants must cite an explicit authority source;
- no row creates command execution, tool invocation, worker assignment,
  dispatch execution, product authorization, external branch activation, PR
  creation, commit, merge, release, benchmark truth, model selection,
  living-memory authority, or recursive policy amendment.

## 7. Fixture And Evidence Strategy

The first `V78-A` reference fixture should remain intentionally small:

- one self-evidencing workflow candidate carried from `V77-C` as blocked or
  eligible-for-authority-review pressure, with no command execution and no tool
  invocation;
- one typed-adjudication product wedge candidate kept future-product-review or
  product-authority-blocked;
- source rows for concrete `V77-C` fixture / closeout / dogfood sources;
- at least one support-context source that cannot make the request eligible by
  itself;
- non-action guardrails with non-empty forbidden runtime actions and
  downstream authority kinds;
- zero authority decision rows, tool-use permission envelopes,
  command-scope authorization boundaries, exception rows, readiness summaries,
  handoffs, command execution, tool invocation, product authorization, release,
  external branch activation, or recursive policy amendment.

`V78-B` and `V78-C` should receive their own future reference / reject fixtures
under their own starter locks.

## 8. Review Questions

- Should a `V78-B` authority decision be allowed to grant bounded later
  execution-review authority, or should all grants remain deferred until a
  later family?
- Should tool-use permission be a separate family, or can it remain a bounded
  `V78-B` envelope as long as no tool invocation happens?
- How should maintainer authority sources be represented without creating a
  live permissioning system inside `packages/adeu_repo_description`?
- What target-specific authority kind is required for external branch pressure
  when `V43` remains conditional?
- Which later family should receive `repo_pre_execution_authority_review_handoff@1`:
  runtime execution review, command-run telemetry, product review, external
  branch review, experiment design, or another family?
