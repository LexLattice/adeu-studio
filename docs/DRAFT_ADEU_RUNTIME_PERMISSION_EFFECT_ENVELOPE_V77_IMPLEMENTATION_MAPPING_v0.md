# Draft ADEU Runtime Permission Effect Envelope V77 Implementation Mapping v0

Status: support / implementation mapping record for planned `V77`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V77` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v67.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RUNTIME_PERMISSION_V77_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V77` should add runtime-permission review and action-effect envelope records
without turning them into:

- command execution;
- runtime permission grant;
- tool-use permission;
- worker assignment or dispatch execution;
- product authorization;
- external branch activation;
- PR creation, commit, merge, release, or released truth;
- relation settlement, claim truth, benchmark truth, or model selection;
- living-memory authority;
- recursive policy amendment.

The implementation target is a typed runtime review family that can represent:

- source-bound runtime permission review requests;
- source indexes that distinguish eligibility sources from support context;
- non-execution guardrails;
- command preflight contracts without command execution;
- action-effect envelopes without accepted effects;
- telemetry requirements without observed telemetry success;
- rollback contracts without rollback verification;
- authority posture without authority grant;
- summary and post-runtime-review handoff rows without later-family authority.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded runtime-permission review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus215/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V77` still describes repo/corpus
metadata and review posture. If a later family becomes live execution,
product UI, external automation, release automation, or graph query runtime,
that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/runtime_permission_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_runtime_permission_review_v77a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_runtime_permission_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_permission_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_non_execution_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_command_preflight_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_action_effect_envelope.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_telemetry_requirement.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_rollback_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_permission_authority_posture.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_permission_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_runtime_permission_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_runtime_permission_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_runtime_permission_review_request.schema.json`
- `spec/repo_runtime_permission_source_index.schema.json`
- `spec/repo_runtime_non_execution_guardrail.schema.json`
- `spec/repo_command_preflight_contract.schema.json`
- `spec/repo_action_effect_envelope.schema.json`
- `spec/repo_runtime_telemetry_requirement.schema.json`
- `spec/repo_runtime_rollback_contract.schema.json`
- `spec/repo_runtime_permission_authority_posture.schema.json`
- `spec/repo_runtime_permission_review_summary.schema.json`
- `spec/repo_post_runtime_permission_review_handoff.schema.json`
- `spec/repo_runtime_permission_family_closeout_alignment.schema.json`

## 3. Candidate `V77` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_runtime_permission_review_request@1` | `V77-A` | runtime-permission review request rows over released `V76-C` handoff and closeout substrate |
| `repo_runtime_permission_source_index@1` | `V77-A` | concrete runtime source rows, absence posture, and source-role classification |
| `repo_runtime_non_execution_guardrail@1` | `V77-A` | non-execution, non-product, non-external, non-release, and non-policy guardrails |
| `repo_command_preflight_contract@1` | `V77-B` | command-intent and preflight contract rows without execution permission |
| `repo_action_effect_envelope@1` | `V77-B` | target, effect, forbidden-effect, and effect-boundary rows for later review |
| `repo_runtime_telemetry_requirement@1` | `V77-B` | telemetry source, checked-surface, and missing-evidence requirements |
| `repo_runtime_rollback_contract@1` | `V77-B` | rollback requirement, rollback source, and blocked rollback posture |
| `repo_runtime_permission_authority_posture@1` | `V77-C` | authority requirement rows without authority grant |
| `repo_runtime_permission_review_summary@1` | `V77-C` | synthesis of runtime review posture without execution |
| `repo_post_runtime_permission_review_handoff@1` | `V77-C` | later-review handoff after runtime permission review |
| `repo_runtime_permission_family_closeout_alignment@1` | `V77-C` | family closeout alignment without runtime execution or release |

`V77-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement command preflight, action
effect envelopes, telemetry, rollback, runtime authority posture, execution,
product workbenching, external branch activation, or release authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V76` reconciliation / arbiter family closeout:
  - `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v214/evidence_inputs/v76_family_closeout_alignment_v214.json`
  - `artifacts/agent_harness/v214/evidence_inputs/v76c_reconciliation_arbiter_closeout_evidence_v214.json`
- `V76-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_review_summary_v214_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus214/repo_post_reconciliation_handoff_v214_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_family_closeout_alignment_v214_reference.json`
- `V72` effect and rollback vocabulary sources:
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_commit_release_authority_posture_v202_reference.json`
- support lineage:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become runtime source rows.

If any expected source is missing when an active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct runtime permission state from planning prose.

## 5. Shared Row Vocabulary

Minimum runtime source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `runtime_source_role`
- `source_horizon`
- `limitation_note`

Minimum runtime permission review request fields:

- `runtime_review_ref`
- `candidate_ref`
- `source_refs`
- `v76_summary_refs`
- `v76_handoff_refs`
- `v76_closeout_refs`
- `requested_permission_horizon`
- `runtime_review_posture`
- `command_intent_kind`
- `command_execution_posture`
- `target_boundary_posture`
- `target_boundary_refs`
- `effect_envelope_needed`
- `telemetry_needed`
- `rollback_needed`
- `required_later_authority_refs`
- `guardrail_refs`
- `odeu_lanes`
- `limitation_note`

Minimum runtime request posture:

- `eligible_for_runtime_permission_review`
- `blocked_by_missing_source`
- `blocked_by_missing_authority`
- `blocked_by_non_runtime_handoff`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum command intent kind:

- `no_command_intent`
- `shell_command_pressure`
- `python_tool_pressure`
- `repo_script_pressure`
- `api_call_pressure`
- `external_tool_pressure`
- `future_family_only`

Minimum command execution posture:

- `no_execution_authorized`
- `execution_requires_later_authority`
- `execution_forbidden_by_this_family`

Starter reference rows should use `command_execution_posture =
no_execution_authorized`.

Minimum non-execution guardrail fields:

- `guardrail_ref`
- `candidate_ref`
- `runtime_review_refs`
- `forbidden_runtime_actions`
- `forbidden_downstream_authority`
- `execution_posture`
- `tool_use_posture`
- `authority_gap_refs`
- `source_refs`
- `limitation_note`

Minimum execution posture:

- `no_execution_authorized`
- `execution_requires_later_authority`
- `execution_forbidden_by_this_family`

Starter reference rows should use `no_execution_authorized`.

## 6. Validation Themes

Expected validators should enforce:

- source rows are explicit and concrete, or carry explicit absence posture;
- support roadmap sources may contextualize `V77` but cannot be the only
  eligibility sources for `eligible_for_runtime_permission_review`;
- runtime review requests reference released `V76-C` summary, handoff, or
  closeout rows, or explicit absence rows;
- product and external branch pressure remains blocked or future-family-only
  unless the row is explicitly routed as future product / external review;
- command intent is not command execution;
- tool applicability is not tool-use permission;
- target boundaries do not authorize file edits or command effects;
- effect envelopes do not claim observed effects;
- telemetry requirements do not claim telemetry success;
- rollback requirements do not claim rollback verification;
- authority posture does not grant authority;
- no row creates command execution, runtime permission grant, worker
  assignment, dispatch execution, product authorization, external branch
  activation, PR creation, commit, merge, release, benchmark truth, model
  selection, living-memory authority, or recursive policy amendment.

## 7. Fixture Plan

First reference fixture should include:

- one self-evidencing workflow-type emergence trace carried from `V76-C` as
  review-only runtime-permission pressure or future-family review pressure;
- one typed-adjudication product wedge trace kept blocked by product authority
  and not treated as runtime permission;
- one source row showing support dogfood context that is not sufficient
  eligibility by itself;
- one non-execution guardrail row with non-empty forbidden runtime and
  downstream authority lists;
- zero command execution, runtime permission grant, tool-use permission,
  product authorization, external branch activation, release, or policy
  amendment rows.

Reject fixtures should cover:

- source-free runtime review request;
- support roadmap source as the only eligibility source;
- product-pressure handoff converted into runtime-ready request;
- command intent treated as command execution;
- guardrail with empty forbidden actions;
- tool applicability converted into tool-use permission;
- local command output treated as permission evidence;
- target glob treated as concrete runtime boundary;
- rollback requirement treated as rollback verification;
- `V77-A` emitting later-slice command preflight or authority posture surfaces.

## 8. Verification Expectation

Docs-only starter bundles should use:

- `make arc-start-check ARC=<n>`

Python implementation PRs should use:

- focused `V77-A` tests plus export-schema tests during development;
- `make check` before PR creation or update.
