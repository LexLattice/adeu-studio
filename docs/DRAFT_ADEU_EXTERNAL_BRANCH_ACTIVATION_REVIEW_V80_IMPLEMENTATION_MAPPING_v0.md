# Draft ADEU External Branch Activation Review V80 Implementation Mapping v0

Status: support / implementation mapping record for planned `V80`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V80` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v70.md`
- `docs/ARCHITECTURE_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V80` should add external branch activation review records without turning them
into:

- external branch activation;
- `V43` contest participation;
- external submission;
- external endpoint mutation;
- external tool invocation for effect;
- external data ingestion or export;
- external result truth;
- command execution, dispatch, product authorization, release, or recursive
  policy amendment;
- `V81` or later-family selection.

The implementation target is a typed external branch review family that can
represent:

- source-bound external branch review requests;
- source indexes that distinguish eligibility sources from roadmap and dogfood
  context;
- non-activation guardrails;
- external data boundaries without transferring data;
- external tool boundaries without invoking tools;
- submission authority review without submission;
- result provenance and withdrawal requirements without external result truth;
- exceptions without resolving them by prose;
- review summaries and post-review handoffs without later-family completion.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded external branch review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus224/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V80` still describes repo/corpus review
metadata and authority posture. If a later family becomes live external
submission automation, external tool invocation, credential handling, product
UI, release automation, or graph query runtime, that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/external_branch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_external_branch_review_v80a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_external_branch_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_non_activation_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_external_data_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_external_tool_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_external_submission_authority_review.v1.json`
- `packages/adeu_repo_description/schema/repo_external_result_provenance_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_readiness_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_external_branch_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_review_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_external_branch_review_request.schema.json`
- `spec/repo_external_branch_source_index.schema.json`
- `spec/repo_external_branch_non_activation_guardrail.schema.json`
- `spec/repo_external_data_boundary.schema.json`
- `spec/repo_external_tool_boundary.schema.json`
- `spec/repo_external_submission_authority_review.schema.json`
- `spec/repo_external_result_provenance_contract.schema.json`
- `spec/repo_external_branch_exception_register.schema.json`
- `spec/repo_external_branch_readiness_summary.schema.json`
- `spec/repo_post_external_branch_review_handoff.schema.json`
- `spec/repo_external_branch_review_family_closeout_alignment.schema.json`

## 3. Candidate `V80` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_external_branch_review_request@1` | `V80-A` | request rows over released `V79-C` substrate and concrete `V43` posture or absence rows |
| `repo_external_branch_source_index@1` | `V80-A` | concrete source rows, absence posture, and source-role classification |
| `repo_external_branch_non_activation_guardrail@1` | `V80-A` | non-activation, non-submission, non-tool-invocation, non-product, non-release, and non-policy guardrails |
| `repo_external_data_boundary@1` | `V80-B` | external data boundary posture without data transfer |
| `repo_external_tool_boundary@1` | `V80-B` | external tool boundary posture without tool invocation |
| `repo_external_submission_authority_review@1` | `V80-B` | submission authority review without submission |
| `repo_external_result_provenance_contract@1` | `V80-B` | result provenance and withdrawal requirements without result truth |
| `repo_external_branch_exception_register@1` | `V80-B` | missing source, branch, data, tool, submission, provenance, withdrawal, product, runtime, and release blockers |
| `repo_external_branch_readiness_summary@1` | `V80-C` | synthesis of external branch review readiness without activation |
| `repo_post_external_branch_review_handoff@1` | `V80-C` | later-review handoff after external branch review |
| `repo_external_branch_review_family_closeout_alignment@1` | `V80-C` | family closeout alignment without external activation or submission |

`V80-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement data boundaries, tool
boundaries, submission authority review, result provenance contracts,
exception registers, summaries, handoffs, external activation, external
submission, external tool invocation, product workbenching, or release
authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V79` controlled execution review family closeout:
  - `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v223/evidence_inputs/v79_family_closeout_alignment_v223.json`
  - `artifacts/agent_harness/v223/evidence_inputs/v79c_controlled_execution_review_closeout_evidence_v223.json`
- `V79-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_summary_v223_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus223/repo_post_controlled_execution_review_handoff_v223_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_family_closeout_alignment_v223_reference.json`
- support lineage:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.json`
- potential `V43` branch-history context:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become external branch source rows.

If a concrete current `V43` / external branch posture source is missing when
an active starter lock is drafted, the absence should be represented as an
explicit source row. The reference fixture should not reconstruct branch
eligibility from planning prose.

## 5. Shared Row Vocabulary

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
`support_process_context` may contextualize `V80-A`; they cannot be the only
sources for `eligible_for_external_branch_review`.

Rows with `external_objective_source` may support request existence and
`request_recorded_objective_only`; they must not by themselves support
`eligible_for_external_branch_review`. Eligible rows require a current
`v43_branch_posture_source`.

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

Minimum branch review posture:

- `request_recorded_objective_only`
- `eligible_for_external_branch_review`
- `blocked_by_missing_source`
- `blocked_by_missing_v43_branch_posture`
- `blocked_by_missing_external_objective`
- `blocked_by_missing_data_boundary`
- `blocked_by_missing_tool_boundary`
- `blocked_by_missing_submission_authority`
- `blocked_by_missing_result_provenance`
- `blocked_by_missing_withdrawal_posture`
- `blocked_by_product_authority_gap`
- `blocked_by_runtime_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum external objective kind:

- `arc_contest_participation_review`
- `external_benchmark_review`
- `external_corpus_ingestion_review`
- `external_tool_endpoint_review`
- `product_externalization_review`
- `external_result_claim_review`
- `future_family_only`

Minimum branch posture currentness:

- `current_branch_posture`
- `historical_branch_planning_context`
- `explicit_absence_marker`
- `stale_or_superseded`
- `unknown_needs_review`

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

Minimum non-activation guardrail fields:

- `guardrail_ref`
- `candidate_ref`
- `source_refs`
- `forbidden_external_actions`
- `forbidden_downstream_authority`
- `guardrail_posture`
- `limitation_note`

## 6. Fixture Strategy

First `V80-A` reference fixture should include:

- one external-branch candidate row that is blocked by missing concrete
  `V43` / external branch posture if no such posture source exists;
- one typed-adjudication product pressure row blocked by product authority or
  rejected as out of scope for external activation;
- source rows for `V79-C` fixtures and family closeout evidence;
- context-only dogfood / roadmap rows that cannot create eligibility by
  themselves;
- explicit `v43_branch_posture_absence_marker` if no concrete branch posture
  source exists;
- non-activation guardrails with non-empty forbidden external actions and
  downstream authority lists;
- zero external submissions, zero external tool invocations, zero external
  endpoint mutations, zero external data transfers, zero result-truth rows,
  zero withdrawal actions, zero product / release rows, and zero later-family
  selections.

Reject fixtures should cover:

- support-only eligibility;
- request without source refs;
- source row without concrete source or explicit absence posture;
- historical `DRAFT_NEXT_ARC_OPTIONS_v43.md` treated as activation authority;
- eligible request without concrete `V43` / external branch posture;
- eligible request supported only by external objective source;
- eligible request whose branch posture currentness is historical, stale,
  unknown, or explicit absence;
- external URL treated as permission;
- external tool boundary treated as invocation;
- submission review treated as submission;
- product pressure marked external-ready;
- controlled execution handoff treated as external execution authority;
- empty forbidden external actions;
- local command or tool output treated as external result evidence.

## 7. Gate Strategy

For initial docs-only family bundle review:

- no active starter lock yet;
- no Python implementation expected.

For the future `V80-A` active starter:

- use canonical starter trio:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS224.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS224.md`
  - `docs/ASSESSMENT_vNEXT_PLUS224_EDGES.md`
- run `make arc-start-check ARC=224` for docs-only starter;
- run `make check` before any Python implementation PR.

## 8. Open Review Questions

- Should `V80-A` include an eligible external branch review row only if a
  concrete current `V43` / external branch posture source exists, or should the
  first fixture be explicitly blocked-only?
- Should `repo_external_result_provenance_contract@1` include withdrawal
  posture, or should withdrawal become its own later surface?
- Should product externalization pressure remain out of scope for `V80`, or
  should it be carried as a blocked external objective with product authority
  gaps?
- Should later actual external participation be possible `V81` pressure, or
  should `V81` remain the cross-corpus governance band named in the roadmap?
