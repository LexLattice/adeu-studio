# Draft ADEU Runtime Permission Effect Envelope V77A Implementation Mapping v0

Status: support note for the planned `V77-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V77-A`
should add runtime permission review requests, runtime source indexes, and
runtime non-execution guardrails after `V76` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v67.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RUNTIME_PERMISSION_V77_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V77-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V77-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. `vNext+215` is the intended scaffold for
that later activation if no intervening arc claims that number.

The active `V77-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That implementation work is
distinct from command preflight, action-effect envelopes, telemetry, rollback,
runtime permission grant, command execution, product authorization, release,
or external branch implementation.

## Candidate New Surfaces

`V77-A` should select:

- `repo_runtime_permission_review_request@1`
- `repo_runtime_permission_source_index@1`
- `repo_runtime_non_execution_guardrail@1`

These surfaces should translate released `V76-C` summary / handoff / closeout
substrate into bounded runtime-permission review posture without granting
runtime permission or executing commands.

## Source Binding

`V77-A` should define explicit runtime source rows over:

- `artifacts/agent_harness/v214/evidence_inputs/v76_family_closeout_alignment_v214.json`
- `artifacts/agent_harness/v214/evidence_inputs/v76c_reconciliation_arbiter_closeout_evidence_v214.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_review_summary_v214_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_post_reconciliation_handoff_v214_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus214/repo_reconciliation_family_closeout_alignment_v214_reference.json`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.json`

Optional context source rows may point at `V72` effect / rollback reference
fixtures to explain vocabulary lineage, but those rows cannot by themselves
make a new `V77-A` request eligible.

Absence should be represented as source posture, not as prose memory.

## Runtime Permission Review Request

The request surface should record:

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

Conditional validation:

- if `runtime_review_posture = eligible_for_runtime_permission_review`, then
  the request must cite at least one released `V76-C` source row and at least
  one non-execution guardrail;
- support / roadmap rows may not be the only source rows for eligibility;
- product-pressure rows must remain `blocked_by_product_authority_gap` or
  `future_family_only` unless explicitly rejected out of scope;
- external-branch rows must remain `blocked_by_external_branch_gap` or
  `future_family_only` unless explicit `V43` branch posture exists;
- `command_intent_kind` records pressure only and must not imply execution;
- `command_execution_posture` must be `no_execution_authorized` in starter
  reference rows;
- known targets may be carried through `target_boundary_refs`, but target refs
  are not permission to change those targets;
- requests must not include command output refs, process IDs, worker assignment
  refs, PR refs, commit refs, merge refs, release refs, product-launch refs, or
  external submission refs.

## Runtime Permission Source Index

The source index should record:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `runtime_source_role`
- `source_horizon`
- `limitation_note`

Minimum source role:

- `v76_summary_source`
- `v76_post_reconciliation_handoff_source`
- `v76_family_closeout_source`
- `v72_effect_surface_context`
- `v72_rollback_context`
- `combined_dogfood_source`
- `support_roadmap_context`
- `absence_marker`

The source index should distinguish eligibility sources from context sources.
Context sources may explain why `V77` exists; they cannot by themselves
authorize runtime review readiness.

## Runtime Non-Execution Guardrail

The guardrail surface should record:

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

- `runtime_permission_grant`
- `product_authorization`
- `external_branch_activation`
- `released_truth`
- `benchmark_truth`
- `model_selection`
- `living_memory_authority`
- `recursive_policy_amendment`

Reference rows should carry:

- `execution_posture = no_execution_authorized`
- `tool_use_posture = tool_use_not_authorized_by_v77`

## Mandatory Reject Cases

- runtime review request with unknown `V76-C` refs;
- runtime review request with no source refs;
- missing source without explicit absence posture;
- support roadmap source as the only eligibility source;
- product-pressure handoff converted into runtime-ready request;
- external-branch pressure converted into runtime-ready request without `V43`
  posture;
- command intent treated as command execution;
- local command output treated as permission evidence;
- worker assignment, dispatch execution, PR, commit, merge, release, product
  launch, or external submission refs inside `V77-A`;
- guardrail with empty forbidden runtime actions;
- guardrail with empty forbidden downstream authority;
- tool applicability converted into tool-use permission;
- `V77-A` fixture emitting `V77-B` command preflight / effect-envelope
  surfaces;
- `V77-A` fixture emitting `V77-C` authority posture / handoff / closeout
  surfaces.

## Reference Fixture Intent

The first fixture should include:

- one self-evidencing workflow-type emergence candidate carried from `V76-C`
  as review-only runtime pressure or future-family review pressure, with no
  command execution and no tool-use permission;
- one typed-adjudication product wedge candidate kept blocked by product
  authority and not treated as runtime permission;
- one support dogfood source row classified as context, not eligibility;
- one non-execution guardrail row with non-empty forbidden runtime actions and
  downstream authority kinds;
- zero command preflight contracts, effect envelopes, telemetry rows, rollback
  rows, runtime authority-posture rows, command execution, runtime permission
  grant, product authorization, release, external branch activation, or
  recursive policy amendment.
