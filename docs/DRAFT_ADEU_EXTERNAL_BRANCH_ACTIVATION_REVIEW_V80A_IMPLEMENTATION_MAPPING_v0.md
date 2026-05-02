# Draft ADEU External Branch Activation Review V80-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V80-A`.

Authority layer: support.

This note does not authorize implementation by itself. It specifies the likely
starter slice that a future `vNext+224` lock may select after the `V80`
family bundle is reviewed.

## Slice Intent

`V80-A` should create the starter schema / model / validator backbone for
external branch activation review intake:

- `repo_external_branch_review_request@1`
- `repo_external_branch_source_index@1`
- `repo_external_branch_non_activation_guardrail@1`

The slice consumes released `V79-C` summary / handoff / closeout substrate and
explicit `V43` / external branch posture or absence rows. It admits external
branch review pressure without creating data boundaries, tool boundaries,
submission authority, result provenance contracts, external activation,
external submission, external tool invocation, product authorization, release,
or later-family selection.

## Expected Files

Implementation files:

- `packages/adeu_repo_description/src/adeu_repo_description/external_branch_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`

Schema files:

- `packages/adeu_repo_description/schema/repo_external_branch_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_external_branch_non_activation_guardrail.v1.json`

Schema mirrors:

- `spec/repo_external_branch_review_request.schema.json`
- `spec/repo_external_branch_source_index.schema.json`
- `spec/repo_external_branch_non_activation_guardrail.schema.json`

Tests:

- `packages/adeu_repo_description/tests/test_external_branch_review_v80a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Fixtures:

- `apps/api/fixtures/repo_description/vnext_plus224/repo_external_branch_review_request_v224_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus224/repo_external_branch_source_index_v224_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus224/repo_external_branch_non_activation_guardrail_v224_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus224/repo_external_branch_v224_reject_*.json`

## Source Basis

Required concrete source rows should cover:

- `docs/DRAFT_ADEU_CONTROLLED_EXECUTION_REVIEW_V79_FAMILY_CLOSEOUT_v0.md`
- `artifacts/agent_harness/v223/evidence_inputs/v79_family_closeout_alignment_v223.json`
- `artifacts/agent_harness/v223/evidence_inputs/v79c_controlled_execution_review_closeout_evidence_v223.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_summary_v223_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_post_controlled_execution_review_handoff_v223_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus223/repo_controlled_execution_review_family_closeout_alignment_v223_reference.json`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_COMBINED_DOGFOOD_TEST_v0.json`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`

Potential branch-history context:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`

`docs/DRAFT_NEXT_ARC_OPTIONS_v43.md` may contextualize branch history, but it
must not be treated as current external branch activation authority by itself.
If no concrete current `V43` / external branch posture source exists, the
starter source index must represent that absence explicitly.

Minimum source roles:

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

An `eligible_for_external_branch_review` row must cite:

- a released `V79-C` summary, handoff, or family-closeout source role; and
- a concrete `v43_branch_posture_source` with
  `branch_posture_currentness = current_branch_posture`.

Context-only dogfood, roadmap, and historical planning rows may not be the
only eligibility basis. A concrete `external_objective_source` may support
request existence and `request_recorded_objective_only`, but it must not by
itself support `eligible_for_external_branch_review`.

`V80-A` should represent later data-boundary, tool-boundary,
submission-authority, result-provenance, and withdrawal pressure through
requested horizons and required postures, not through refs to `V80-B` surfaces
that do not exist yet.

Required starter request fields include:

- `branch_posture_currentness`
- `requested_data_boundary_horizon`
- `requested_tool_boundary_horizon`
- `requested_submission_authority_horizon`
- `required_result_provenance_posture`
- `required_withdrawal_posture`
- `external_activation_posture`
- `external_submission_posture`
- `external_tool_invocation_posture`

Reference rows must carry:

- `external_activation_posture =
  no_external_branch_activation_performed_by_v80`
- `external_submission_posture = no_external_submission_performed_by_v80`
- `external_tool_invocation_posture =
  no_external_tool_invocation_performed_by_v80`
- `execution_posture = no_execution_performed_by_v80`

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
- eligible requests reference released `V79-C` summary, handoff, or closeout
  refs and a matching eligibility source role;
- eligible requests include concrete current `V43` / external branch posture;
- external objective source refs alone support only objective-only request
  posture, not eligibility;
- support-only sources cannot make a request eligible;
- a historical `DRAFT_NEXT_ARC_OPTIONS_v43.md` row cannot be activation
  authority by itself;
- product pressure cannot be marked external-activation-ready;
- controlled execution handoffs cannot be marked external activation
  authority;
- all request rows carry no-activation, no-submission, no-external-tool, and
  no-execution posture;
- guardrail rows reference known candidates and source rows;
- data-boundary, tool-boundary, submission-authority, result-provenance,
  withdrawal, and exception refs are absent from `V80-A` request rows;
- no `V80-A` row contains external activation, external submission, external
  endpoint mutation, external tool invocation, command execution, tool
  invocation, dispatch, PR, commit, merge, release, product authorization,
  benchmark truth, model selection, living-memory authority, recursive policy
  amendment, or `V81` selection fields.

## Reference Fixture Intent

The first reference fixture should include:

- one external branch review candidate blocked by missing concrete `V43` /
  external branch posture if no such source exists;
- one objective-only row if a concrete external objective exists without
  current `V43` posture;
- one typed-adjudication product wedge candidate blocked by product authority
  or rejected as out of scope for external activation;
- source rows for `V79-C` fixtures and family closeout evidence;
- context-only dogfood / roadmap rows;
- an explicit `v43_branch_posture_absence_marker` row when appropriate;
- non-activation guardrails for both candidates.

The fixture should include zero external submissions, external tool
invocations, external endpoint mutations, external data transfers, result-truth
rows, withdrawal actions, worker assignments, dispatch executions, product
authorizations, external branch activations, PR / commit / merge / release
rows, benchmark truth rows, global model selection rows, living-memory rows,
recursive policy amendment rows, or `V81` selection rows.

## Mandatory Reject Fixtures

- request with no source refs;
- source row without concrete source or explicit absence posture;
- eligible request sourced only by support dogfood or roadmap context;
- historical `DRAFT_NEXT_ARC_OPTIONS_v43.md` treated as activation authority;
- eligible request without concrete current `V43` / external branch posture;
- eligible request supported only by external objective source;
- eligible request whose branch posture currentness is historical, stale,
  unknown, or explicit absence;
- external URL or endpoint string treated as permission;
- external tool boundary treated as tool invocation;
- submission review treated as submission;
- product pressure marked external-ready;
- controlled execution handoff treated as external execution authority;
- empty forbidden external actions;
- non-empty data-boundary, tool-boundary, submission-authority,
  result-provenance, withdrawal, or exception refs in a `V80-A` request row;
- row claiming external activation, external submission, or external tool
  invocation;
- row selecting `V80-B`, `V80-C`, `V81`, product review, external branch
  activation, or release authority.

## Non-Selection

`V80-A` does not select `V80-B`, `V80-C`, external activation, external
submission, external tool invocation, data transfer, result truth, data
boundaries, tool boundaries, submission authority records, result provenance
contracts, exception registers, summaries, handoffs, product authorization,
release, dispatch, living memory, recursive policy amendment, or any later
family.
