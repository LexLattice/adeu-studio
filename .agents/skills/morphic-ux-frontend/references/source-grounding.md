# Morphic UX Source Grounding

This file captures the current repo-native reference family that the skill should treat as ground truth when no newer contract supersedes it.

## Primary sources

- `apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json`
- `apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json`
- `apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json`
- `apps/api/fixtures/ux_governance/vnext_plus61/v36a_same_context_reachability_glossary.json`
- `apps/api/fixtures/ux_governance/vnext_plus62/ux_surface_projection_artifact_inspector_reference.json`
- `apps/web/src/app/artifact-inspector/reference-surface.ts`
- `apps/web/src/app/artifact-inspector/page.tsx`
- `apps/web/src/app/artifact-inspector/page.module.css`
- `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py`
- `packages/adeu_core_ir/tests/test_ux_governance.py`
- `packages/adeu_core_ir/tests/test_ux_governance_evidence.py`
- `docs/seed arc v10.md`

## Reference family

- `reference_surface_family`: `artifact_inspector_advisory_workbench`
- `reference_instance_id`: `artifact_inspector_reference_main`
- `primary_user_archetype`: `expert_operator`
- `device_class`: `desktop`
- `risk_level`: `high`
- `trust_sensitivity`: `authority_and_evidence_sensitive`
- `interaction_mode`: `analysis_then_commit`
- `utility_ranking`:
  - `trust_calibration`
  - `error_prevention`
  - `operator_speed`

## Frozen authority policy

All current released UX artifacts bind the same policy:

- `no_free_form_ui_codegen_without_ir = true`
- `no_visual_authority_inflation = true`
- `ui_artifacts_may_express_but_may_not_mint_authority = true`

Treat this as doctrine, not a styling preference.

## Frozen invariants

- `destructive_action_gating`
- `evidence_before_commit_visibility`
- `observable_state_transitions`
- `trust_boundary_clarity`
- `unambiguous_primary_action`

## Allowed morph axes

- `density`
- `navigation_mode`
- `information_posture`
- `interaction_tempo`
- `salience_posture`
- `state_exposure`
- `command_posture`

## Approved profiles

### `artifact_inspector_reference`

- `density = high`
- `navigation_mode = split_pane`
- `information_posture = evidence_first`
- `interaction_tempo = expert_fast_path`
- `salience_posture = evidence_and_status_prominent`
- `state_exposure = full_explicit`
- `command_posture = dual_lane`

### `artifact_inspector_alternate`

- `density = medium`
- `navigation_mode = hub_and_spoke`
- `information_posture = task_first`
- `interaction_tempo = guided`
- `salience_posture = action_and_diagnostics_prominent`
- `state_exposure = progressive`
- `command_posture = safe_buffered`

Do not mix profile values ad hoc unless the task is explicitly about extending the approved table.

## Same-context glossary

### Same-context reachable

- `bounded_workbench_focus_shift`
- `bounded_workbench_position_shift`
- `bounded_workbench_state_reveal`

### Context break

- `bounded_workbench_replacement`
- `detached_surface_replacement`
- `route_transition`

### Forbidden barrier

- `authority_escalation_step`
- `cross_workbench_dependency`

### Commit or destructive barrier

- `commit_action`
- `destructive_action`

These terms are validated as substrate-level semantics. Do not rewrite them into widget-level language such as "tab", "drawer", or "modal".

## Current reference topology

### Regions

- `navigation_region`
- `action_region`
- `primary_work_region`
- `evidence_region`
- `status_region`

### Lanes

- `navigation-lane`
- `action-lane`
- `source-lane`
- `work-context-lane`
- `diagnostics-lane`
- `evidence-lane`
- `status-lane`
- `trust-boundary-lane`

### Action clusters

- `advisory-actions`
- `commit-actions`
- `comparison-actions`

### State surfaces

- `authoritative-status-surface`
- `diagnostic-status-surface`
- `provisional-status-surface`
- `warning-status-surface`

### Responsive doctrine

The reference CSS preserves the bounded workbench while adapting:

- desktop: three-column workbench
- mid-width: two-column workbench
- narrow-width: single-column workbench

The important point is not the exact grid. The important point is that evidence and state surfaces remain reachable without a route change.

## What the source code demonstrates

- `page.tsx` renders identity, region markers, evidence lanes, status surfaces, and an explicit commit gate as first-class structure.
- `reference-surface.ts` enforces binding and provenance targets such as evidence-bearing regions, state distinction surfaces, authority-bearing controls, and required evidence anchors.
- `ux_governance.py` freezes the current morph axes, epistemic states, authority policy, and same-context glossary.
- the governance evidence tests fail closed when authority inflation, free-form bypass, or glossary drift appears

The lesson for frontend work is simple: visual design is allowed to morph only after those bindings are respected.
