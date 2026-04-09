# Morphic UX Governed Enactment Burden Log Template v0

Use this template during one governed-enactment run under:

- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md`

and usually paired with:

- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_TASK_CORPUS_v0.md`

This template is support-layer only. Filling it does not authorize new tool surfaces by
itself.

---

## Run Metadata

- `run_id`:
- `task_id`:
- `run_date_utc`:
- `skill_path`:
- `skill_revision_note`:
- `task_mode`:
  - `design`
  - `implementation`
  - `review`
- `execution_mode`:
  - `governed_enactment`
- `model_id`:
- `grounding_status`:
  - `repo_grounded`
  - `artifact_grounded_repo_incomplete`
  - `inference_only`
- `implementation_inspection_status`:
  - `implementation_inspected`
  - `implementation_not_inspected`
- `snapshot_stance`:
- `target_scope`:

## Frozen World

- authoritative lock docs:
- authoritative released artifacts:
- accepted support docs:
- explicit exclusions:

## Task Summary

- claimed task:
- observed reachable surfaces:
- shipped or proposed scope:
- final task outcome:
- overall burden judgment:
  - `stable_enough`
  - `tool_pressure_visible`
  - `skill_gap_dominant`
  - `mixed`

---

## Burden Entries

Copy the block below once per burden family detected during the run.

### `burden_entry_<n>`

- `burden_id`:
- `operation_family`:
- `detected_in_step`:
- `reasoning_lane`:
  - `frozen_world`
  - `settlement`
  - `observation`
  - `intended_interpretation`
  - `alignment`
  - `implementation`
  - `final_summary`
- `repeated_simulation_burden`:
- `why_this_feels_like_infrastructure_not_normal_reading`:
- `current_manual_workaround`:
- `source_refs`:
- `recurrence_within_task`:
- `similar_prior_occurrences`:
- `impact_if_missing`:
- `top_level_bin`:
  - `tool_candidate`
  - `skill_gap`
  - `unresolved`
- `classification`:
  - `lawful_required`
  - `reliable_required`
  - `performance_only`
  - `skill_gap`
  - `unresolved`
- `minimal_inputs`:
- `minimal_outputs`:
- `adjacent_non_goals`:
- `recommended_next_action`:
  - `promote_minimal_tool_candidate`
  - `clarify_skill`
  - `collect_more_runs`
  - `reject_as_one_off`
- `notes`:

---

## Aggregated Candidate Surfaces

Fill this section only after the individual burden entries are written.

### `candidate_surface_<n>`

- `candidate_id`:
- `operation_family`:
- `derived_from_burden_ids`:
- `classification`:
  - `lawful_required`
  - `reliable_required`
  - `performance_only`
  - `unresolved`
- `minimal_interface_statement`:
- `required_inputs`:
- `required_outputs`:
- `non_goals`:
- `why_not_just_skill_text`:
- `recurrence_evidence`:
- `retest_required`:

---

## Skill-Gap Findings

List burdens that should not become tools because the real problem is missing or weak
skill instruction.

- `skill_gap_<n>`:
  - problem:
  - suggested skill clarification:
  - burden_ids:

---

## Promotion Summary

- `lawful_required_candidates`:
- `reliable_required_candidates`:
- `performance_only_candidates`:
- `skill_gap_count`:
- `retest_subset_recommended`:
- `final_promotion_note`:

## Compact One-Paragraph Closeout

Write one short paragraph answering:

- what the agent kept having to simulate;
- which burdens look like real support-layer gaps;
- which burdens look like skill clarifications instead;
- what the next minimal retest should be.
