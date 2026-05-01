# Draft ADEU Runtime Execution Authority V78A Implementation Mapping v0

Status: support note for the planned `V78-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V78-A`
should add runtime execution authority requests, runtime authority source
indexes, and runtime authority non-action guardrails after `V77` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V78-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V78-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. `vNext+218` is the intended scaffold for
that later activation if no intervening arc claims that number.

The active `V78-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That implementation work is
distinct from authority decisions, tool-use permission envelopes,
command-scope authorization boundaries, runtime authority exception registers,
command execution, product authorization, release, or external branch
implementation.

## Candidate New Surfaces

`V78-A` should select:

- `repo_runtime_execution_authority_request@1`
- `repo_runtime_authority_source_index@1`
- `repo_runtime_authority_non_action_guardrail@1`

These surfaces should translate released `V77-C` authority / summary /
handoff / closeout substrate into bounded runtime execution authority request
posture without granting authority, invoking tools, or executing commands.

## Source Binding

`V78-A` should define explicit runtime authority source rows over:

- `artifacts/agent_harness/v217/evidence_inputs/v77_family_closeout_alignment_v217.json`
- `artifacts/agent_harness/v217/evidence_inputs/v77c_runtime_permission_closeout_evidence_v217.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_authority_posture_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_review_summary_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_post_runtime_permission_review_handoff_v217_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus217/repo_runtime_permission_family_closeout_alignment_v217_reference.json`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json`

Optional context source rows may point at `V77-B` preflight / effect /
telemetry / rollback reference fixtures to explain scope vocabulary lineage,
but those rows cannot by themselves make a new `V78-A` request eligible.

Absence should be represented as source posture, not as prose memory.

## Runtime Execution Authority Request

The request surface should record:

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

Conditional validation:

- if `authority_request_posture =
  eligible_for_runtime_execution_authority_review`, then the request must cite
  at least one released `V77-C` source row and at least one non-action
  guardrail;
- support / roadmap rows may not be the only source rows for eligibility;
- product-pressure rows must remain `blocked_by_product_authority_gap` or
  `future_family_only` unless explicitly rejected out of scope;
- external-branch rows must remain `blocked_by_external_branch_gap` or
  `future_family_only` unless explicit `V43` branch posture exists;
- command preflight refs may inform request scope but must not imply execution;
- `execution_posture` must be `no_execution_performed_by_v78` in starter
  reference rows;
- `tool_invocation_posture` must be `no_tool_invocation_performed_by_v78` in
  starter reference rows;
- known targets may be carried through `target_boundary_refs`, but target refs
  are not permission to change those targets;
- requests must not include command output refs, process IDs, worker assignment
  refs, PR refs, commit refs, merge refs, release refs, product-launch refs, or
  external submission refs.

## Authority Requirement Rows

`V78-A` should include embedded authority requirement rows so
`required_authority_source_refs` cannot become a free-text bucket.

Minimum authority requirement row fields:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_for_horizon`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum `authority_kind`:

- `maintainer_authority`
- `policy_authority`
- `runtime_execution_review_authority`
- `tool_use_review_authority`
- `product_authorization`
- `external_branch_activation`
- `release_authority`
- `recursive_policy_authority`

Reference rows should source-bind authority requirements through concrete
`V77-C` rows or explicit absence markers.

## Runtime Authority Source Index

The source index should record:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `runtime_authority_source_role`
- `source_horizon`
- `limitation_note`

Minimum source role:

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

The source index should distinguish authority eligibility sources from context
sources. Context sources may explain why `V78` exists; they cannot by
themselves authorize authority-review readiness.

## Runtime Authority Non-Action Guardrail

The guardrail surface should record:

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

Minimum `forbidden_runtime_actions` should include:

- `run_command`
- `invoke_tool_for_effect`
- `assign_worker`
- `dispatch_worker`
- `open_pr`
- `commit`
- `merge`
- `release`
- `external_submission`

Minimum `forbidden_downstream_authority` should include:

- `product_authorization`
- `external_branch_activation`
- `released_truth`
- `benchmark_truth`
- `model_selection`
- `living_memory_authority`
- `recursive_policy_amendment`

Reference rows should carry:

- `execution_posture = no_execution_performed_by_v78`
- `tool_invocation_posture = no_tool_invocation_performed_by_v78`

## Mandatory Reject Cases

- runtime execution authority request with unknown `V77-C` refs;
- runtime execution authority request with no source refs;
- missing source without explicit absence posture;
- support context as the only eligibility source;
- product-pressure handoff converted into runtime-authority-ready request;
- external-branch pressure converted into runtime-authority-ready request
  without `V43` posture;
- command preflight treated as command execution;
- tool-use request treated as tool invocation;
- local command output treated as authority evidence;
- support / dogfood source as the only eligibility source;
- command preflight plus target refs treated as command-scope authorization;
- worker assignment, dispatch execution, PR, commit, merge, release, product
  launch, or external submission refs inside `V78-A`;
- guardrail with empty forbidden runtime actions;
- guardrail with empty forbidden downstream authority;
- `V78-A` fixture emitting `V78-B` authority decision / tool-use permission /
  command-scope surfaces;
- `V78-A` fixture emitting `V78-C` readiness / handoff / closeout surfaces.

## Reference Fixture Intent

The first fixture should include:

- one self-evidencing workflow-type emergence candidate carried from `V77-C`
  as runtime / tool-use authority pressure, with no command execution and no
  tool invocation;
- one typed-adjudication product wedge candidate kept blocked by product
  authority and not treated as runtime execution authority;
- one support dogfood source row classified as context, not eligibility;
- one non-action guardrail row with non-empty forbidden runtime actions and
  downstream authority kinds;
- zero authority decisions, tool-use permission envelopes, command-scope
  boundaries, exception rows, readiness summaries, handoffs, command
  execution, tool invocation, product authorization, release, external branch
  activation, or recursive policy amendment.
