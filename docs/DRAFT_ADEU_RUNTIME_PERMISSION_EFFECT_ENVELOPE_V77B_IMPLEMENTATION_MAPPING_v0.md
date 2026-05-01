# Draft ADEU Runtime Permission Effect Envelope V77B Implementation Mapping v0

Status: support note for the planned `V77-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V77-B`
should add command preflight contracts, action-effect envelopes, runtime
telemetry requirements, and runtime rollback contracts after `V77-A` has
closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v67.md`
- `docs/ARCHITECTURE_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RUNTIME_PERMISSION_EFFECT_ENVELOPE_V77A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V77-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

`V77-B` should become active only after `V77-A` has shipped source-bound
runtime permission review request, runtime source index, and non-execution
guardrail rows. The active `V77-B` lock should select only preflight and
effect-envelope review records. It must not grant runtime permission or run
commands.

## Candidate New Surfaces

`V77-B` should select:

- `repo_command_preflight_contract@1`
- `repo_action_effect_envelope@1`
- `repo_runtime_telemetry_requirement@1`
- `repo_runtime_rollback_contract@1`

These surfaces should extend released `V77-A` rows. They should not create a
parallel runtime universe that bypasses `V77-A` source indexes or
non-execution guardrails.

## Command Preflight Contract

The command preflight contract should record:

- `preflight_ref`
- `runtime_review_refs`
- `candidate_ref`
- `command_intent_kind`
- `command_intent_label`
- `command_ref_posture`
- `target_boundary_refs`
- `target_resolution_kind`
- `required_source_refs`
- `required_authority_refs`
- `required_telemetry_refs`
- `required_rollback_refs`
- `preflight_posture`
- `execution_posture`
- `forbidden_inferences`
- `limitation_note`

Minimum command intent kind:

- `no_command_intent`
- `shell_command_later_review`
- `python_tool_later_review`
- `repo_script_later_review`
- `api_call_later_review`
- `external_tool_later_review`
- `future_family_only`

Minimum preflight posture:

- `preflight_contract_for_review_only`
- `preflight_blocked_by_missing_source`
- `preflight_blocked_by_missing_authority`
- `preflight_blocked_by_target_boundary`
- `preflight_blocked_by_missing_telemetry`
- `preflight_blocked_by_missing_rollback`
- `preflight_future_family_only`
- `preflight_rejected_out_of_scope`

Minimum target resolution kind:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `concrete_script_ref`
- `bounded_package_surface_with_child_refs`
- `external_endpoint_ref`
- `no_target_boundary`

Every reference row should carry:

- `execution_posture = no_execution_authorized`

If `command_intent_kind != no_command_intent`, then target boundary refs must
be non-empty or `target_resolution_kind` must be `no_target_boundary` with a
blocker posture. If `target_resolution_kind =
bounded_package_surface_with_child_refs`, concrete child refs must be present.
Globs may be discovery context only, not target boundaries.

## Action-Effect Envelope

The action-effect envelope should record:

- `effect_envelope_ref`
- `runtime_review_refs`
- `preflight_refs`
- `candidate_ref`
- `target_boundary_refs`
- `allowed_effect_surface_refs`
- `forbidden_effect_surface_refs`
- `effect_horizon`
- `effect_envelope_posture`
- `effect_acceptance_posture`
- `source_refs`
- `non_execution_guardrail_refs`
- `limitation_note`

Minimum effect envelope posture:

- `effect_envelope_for_review_only`
- `effect_envelope_blocked_by_missing_target`
- `effect_envelope_blocked_by_missing_telemetry`
- `effect_envelope_blocked_by_missing_rollback`
- `effect_envelope_future_family_only`
- `effect_envelope_rejected_out_of_scope`

Minimum effect acceptance posture:

- `no_effect_accepted`
- `effect_requires_later_review`
- `effect_not_observed`
- `effect_observed_from_prior_authorized_artifact`

An effect envelope is a review object. It is not accepted effect, not runtime
permission, and not permission to edit files.

## Runtime Telemetry Requirement

The telemetry requirement should record:

- `telemetry_requirement_ref`
- `runtime_review_refs`
- `preflight_refs`
- `effect_envelope_refs`
- `candidate_ref`
- `telemetry_surface_kind`
- `required_telemetry_source_refs`
- `checked_source_refs`
- `missing_source_refs`
- `telemetry_posture`
- `limitation_note`

Minimum telemetry posture:

- `telemetry_required_later`
- `telemetry_source_present_for_prior_artifact`
- `telemetry_missing_expected_source`
- `telemetry_not_applicable`
- `telemetry_future_family_only`

Telemetry requirements must not claim that telemetry has succeeded unless they
point to a prior authorized source artifact. A future command cannot be treated
as having telemetry just because a row names a telemetry requirement.

## Runtime Rollback Contract

The rollback contract should record:

- `rollback_contract_ref`
- `runtime_review_refs`
- `preflight_refs`
- `effect_envelope_refs`
- `candidate_ref`
- `rollback_surface_kind`
- `required_rollback_source_refs`
- `rollback_posture`
- `blocking_gap_refs`
- `limitation_note`

Minimum rollback posture:

- `rollback_required_later`
- `rollback_source_present_for_prior_artifact`
- `rollback_missing_expected_source`
- `rollback_blocked`
- `rollback_not_applicable`
- `rollback_future_family_only`

Rollback contracts must not claim rollback verification unless they point to a
prior authorized source artifact. A rollback plan is not rollback proof.

## Mandatory Reject Cases

- preflight row without known `V77-A` runtime review refs;
- preflight row without non-execution guardrail refs;
- command intent treated as command execution;
- command string or script path treated as permission to run;
- target glob treated as concrete target boundary;
- effect envelope without target boundary or explicit no-target posture;
- effect envelope claiming accepted effect;
- telemetry requirement claiming success without source artifact;
- rollback contract claiming verified rollback without source artifact;
- runtime permission grant emitted by `V77-B`;
- tool-use permission emitted by `V77-B`;
- product authorization, external activation, PR creation, commit, merge, or
  release emitted by `V77-B`;
- `V77-B` fixture emitting `V77-C` authority posture / summary / handoff /
  closeout surfaces.

## Reference Fixture Intent

The first `V77-B` fixture should include:

- one review-only command preflight contract for a candidate admitted by
  `V77-A`, with `execution_posture = no_execution_authorized`;
- one action-effect envelope with explicit allowed and forbidden effect
  surfaces;
- one telemetry requirement row that says telemetry is required later, not
  observed now;
- one rollback contract row that says rollback is required later, not verified
  now;
- one blocked product / external / authority example carried as future-family
  only;
- zero command execution, runtime permission grant, worker assignment, dispatch
  execution, product authorization, external branch activation, release, or
  recursive policy amendment.
