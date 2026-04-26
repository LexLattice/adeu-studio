# Review GPTPro Contained Integration Review V72 Planning v0

Status: support review captured for the planned `V72` family.

Authority layer: support.

This review approves `V72` as the correct next family after closed `V68`,
`V69`, `V70`, and `V71`, while keeping the current bundle below active
implementation-lock authority until the future `vNext+200` starter trio exists.

## Verdict

The review approves the family direction: `V72` should bridge ratified /
handed-off candidates into bounded integration planning without becoming merge,
release, product, runtime, or dispatch authority. `V72-A` remains the only
immediate starter target.

## Required Patches Before `vNext+200`

- Distinguish active-slice implementation of `V72-A` schemas from candidate
  contained-integration trial work.
- Add or embed `integration_source_rows` so plan, target-boundary, guardrail,
  and handoff refs resolve through concrete source rows or explicit absence
  rows.
- Split `required_trial_posture` in `V72-A` from actual `trial_posture` in
  `V72-B`.
- Add conditional validation for eligible, blocked, and future-family-only
  containment plans.
- Add `target_resolution_kind` so `package_surface` cannot become a broad
  unbounded target.
- Require `rollback_requirement` in every eligible `V72-A` plan, while
  forbidding `V72-A` from claiming rollback verification.
- Add `trial_diff_posture` or equivalent in `V72-B` to distinguish proposed,
  local, accepted-for-review, reverted, and rejected diffs.
- Require `local_trial_recorded` rows to cite active lock/source evidence,
  target boundaries, and non-release guardrails.
- Split `commit_release_posture` in `V72-C` into commit, PR, merge, release,
  and released-truth fields.
- Require maintainer / human authority refs to resolve to concrete source or
  authority-profile rows.

## Starter Scope Recommendation

The future `vNext+200` lock should select only:

- `repo_contained_integration_candidate_plan@1`
- `repo_integration_target_boundary@1`
- `repo_integration_non_release_guardrail@1`

It should not select trial execution, `V72-B`, `V72-C`, commit / PR / merge /
release posture, `V73` outcome review, product projection, runtime permission,
dispatch, or external contest participation.
