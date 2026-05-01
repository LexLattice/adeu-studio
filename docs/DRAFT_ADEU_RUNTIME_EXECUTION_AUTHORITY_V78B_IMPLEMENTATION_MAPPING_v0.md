# Draft ADEU Runtime Execution Authority V78B Implementation Mapping v0

Status: support note for the planned `V78-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V78-B`
should add runtime execution authority decisions, tool-use permission
envelopes, command-scope authorization boundaries, and runtime authority
exception registers after `V78-A` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v68.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_EXECUTION_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_EXECUTION_AUTHORITY_V78A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V78-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V78-B` becomes active, it should receive its own canonical starter trio
after `V78-A` has merged and lean-closed. It must consume released `V78-A`
request, source, and guardrail rows; it must not create a parallel authority
universe.

## Candidate New Surfaces

`V78-B` should select:

- `repo_runtime_execution_authority_decision@1`
- `repo_tool_use_permission_envelope@1`
- `repo_command_scope_authorization_boundary@1`
- `repo_runtime_authority_exception_register@1`

These surfaces should decide or block bounded later execution-review authority
without executing commands or invoking tools.

## Runtime Execution Authority Decision

The decision surface should record:

- `authority_decision_ref`
- `authority_request_refs`
- `candidate_ref`
- `decision_posture`
- `decision_horizon`
- `authority_source_refs`
- `authority_actor_refs`
- `tool_use_permission_refs`
- `command_scope_boundary_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `exception_refs`
- `execution_posture`
- `non_execution_guardrail_refs`
- `limitation_note`

Minimum `decision_posture`:

- `review_authority_granted_for_bounded_execution_surface`
- `review_authority_denied`
- `review_authority_deferred`
- `review_authority_blocked_by_missing_source`
- `review_authority_blocked_by_missing_scope`
- `review_authority_blocked_by_missing_telemetry`
- `review_authority_blocked_by_missing_rollback`
- `review_authority_future_family_only`
- `review_authority_rejected_out_of_scope`

Every decision row should also carry:

- `authorized_surface_kind`
- `authority_grant_horizon`
- `execution_authorization_posture`

Minimum `authorized_surface_kind`:

- `later_execution_review_surface`
- `later_tool_invocation_review_surface`
- `later_telemetry_review_surface`
- `later_rollback_review_surface`
- `future_family_review_surface`

Minimum `execution_authorization_posture`:

- `execution_not_authorized_by_v78`
- `execution_requires_later_family`
- `execution_forbidden_by_this_family`

Reference rows should use `execution_authorization_posture =
execution_not_authorized_by_v78`.

Validation:

- every decision must reference a known `V78-A` authority request;
- any grant posture must cite concrete authority source refs and non-action
  guardrail refs;
- grant posture must include bounded command-scope refs and cannot use globs as
  target boundaries;
- grant posture must include a later-review-only `authorized_surface_kind` or
  `authority_grant_horizon`;
- grant posture must carry `execution_posture =
  no_execution_performed_by_v78`;
- product and external authority gaps cannot be converted into runtime
  execution authority grants;
- a model suggestion, transcript, passing command output, or local tool result
  cannot be the sole authority source.

## Tool-Use Permission Envelope

The tool-use permission envelope should record:

- `tool_permission_ref`
- `authority_request_refs`
- `candidate_ref`
- `tool_id`
- `tool_target_horizon`
- `tool_target_refs`
- `permission_posture`
- `permission_scope_boundary_refs`
- `authority_source_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `exception_refs`
- `tool_invocation_posture`
- `limitation_note`

Minimum `permission_posture`:

- `tool_use_permission_granted_for_later_execution_review`
- `tool_use_permission_denied`
- `tool_use_permission_deferred`
- `tool_use_permission_blocked_by_missing_authority`
- `tool_use_permission_future_family_only`
- `tool_use_not_applicable`

Validation:

- tool permission must be horizon-bound and target-bound;
- global tool permission must reject;
- permission posture must not imply tool invocation;
- external tool use must remain blocked or future-family-only unless concrete
  authority source refs exist;
- tool applicability from `V75` or `V77` is not tool-use permission.

## Command-Scope Authorization Boundary

The command-scope boundary should record:

- `command_scope_ref`
- `authority_request_refs`
- `candidate_ref`
- `command_intent_kind`
- `target_resolution_kind`
- `target_refs`
- `authorized_scope_posture`
- `allowed_effect_surface_refs`
- `forbidden_effect_surface_refs`
- `telemetry_requirement_refs`
- `rollback_requirement_refs`
- `authority_source_refs`
- `exception_refs`
- `execution_posture`
- `limitation_note`

Minimum `authorized_scope_posture`:

- `bounded_scope_authorized_for_later_execution_review`
- `scope_denied`
- `scope_deferred`
- `scope_blocked_by_missing_target`
- `scope_blocked_by_unbounded_target`
- `scope_blocked_by_missing_telemetry`
- `scope_blocked_by_missing_rollback`
- `scope_future_family_only`

Validation:

- bounded scope must cite concrete target refs;
- `bounded_package_surface_with_child_refs` must include concrete child refs;
- globs are discovery context only and must reject as scope authorization;
- command-scope authorization is not command execution;
- target scope is not permission to mutate target state inside `V78`.

## Runtime Authority Exception Register

The exception register should record:

- `exception_ref`
- `candidate_ref`
- `authority_request_refs`
- `exception_kind`
- `exception_posture`
- `blocking_surface_refs`
- `source_refs`
- `required_next_surface`
- `limitation_note`

Minimum `exception_kind`:

- `missing_authority_source`
- `missing_command_scope`
- `unbounded_target`
- `missing_telemetry_requirement`
- `missing_rollback_requirement`
- `tool_permission_gap`
- `product_authority_gap`
- `external_branch_authority_gap`
- `release_authority_gap`
- `command_output_without_prior_authority`
- `unknown_needs_review`

Exceptions may be blocking, warning-only, carried-forward, not applicable, or
future-family-only. They must not be marked resolved by `V78-B` unless the
resolution is represented by a concrete `V78-B` decision row and still does
not imply execution.

## Mandatory Reject Cases

- authority decision without a known `V78-A` request;
- authority grant without concrete authority source refs;
- authority grant plus command-scope refs without explicit later-review-only
  horizon;
- authority grant with unbounded or glob target scope;
- authority grant that implies command execution or tool invocation;
- tool-use envelope that grants global tool permission;
- tool-use permission inferred from tool applicability;
- command-scope boundary with no telemetry or rollback posture where those are
  required by the source request;
- product or external branch pressure granted as runtime execution authority;
- local command output treated as authority evidence;
- exception row marked resolved by prose only;
- `V78-B` fixture emitting `V78-C` readiness / handoff / closeout surfaces.

## Reference Fixture Intent

The first `V78-B` fixture should include:

- one self-evidencing workflow candidate with a bounded later-execution-review
  authority decision or a blocked decision that preserves missing authority;
- one tool-use permission envelope that is target-bound and does not invoke a
  tool;
- one command-scope boundary with concrete target refs and non-execution
  posture;
- one product wedge row kept blocked by product authority or future-product
  review;
- one exception row for a missing or deferred authority surface;
- zero command execution, tool invocation, worker assignment, dispatch
  execution, product authorization, external branch activation, PR, commit,
  merge, release, benchmark truth, model selection, living-memory authority, or
  recursive policy amendment.
