# Draft Next Arc Options v62

Status: planning handoff after `vNext+199` / `V71-C` merged on `main` and after
the `V71` family closeout pass.

Authority layer: planning.

This draft records the post-`V71` frontier. It does not authorize
implementation, contained integration execution, commit / merge / release
authority, product projection, runtime permission, dispatch widening, or
external contest participation by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v61.md`, which selected the `V71` family. `vNext+197`,
`vNext+198`, and `vNext+199` then closed `V71-A`, `V71-B`, and `V71-C` without
creating additional family selector versions.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- latest closed implementation arc: `vNext+199`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v61.md`
- next planning obligation: select and review `V72` as the next family outside
  closed `V71`.

The combined `V68` / `V69` / `V70` / `V71` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 contained-integration-review pressure
```

## Next Planning Question

Now that candidate pressure can be mapped, admitted, reviewed, ratified,
deferred, rejected, and handed off without adoption or implementation, should
the next family be `V72`: contained integration review, rollback readiness, and
commit / release authority boundary?

## Recommended Next Pressure

- family: `V72`
- proposed family name:
  - `V72: contained integration review, rollback readiness, and commit/release
    authority boundary`
- recommended planning posture:
  - select `V72` as the next family for support review;
  - treat `V72-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake as admitted candidate substrate;
  - consume `V70` review classification as evidence / gap substrate;
  - consume `V71` ratification, amendment-scope, and handoff surfaces as
    integration-review substrate;
  - plan and bound contained integration review without performing unbounded
    implementation, merge, release, product projection, runtime permission, or
    dispatch.

## Why `V72` Now

`V68` tells the repo where sources and authority boundaries sit. `V69` admits
candidate pressure without adoption. `V70` classifies evidence, adversarial
review, conflict, complementarity, gaps, and pre-ratification handoff. `V71`
records ratification, deferral, dissent, amendment scope, and post-ratification
handoff.

The next bottleneck is contained integration review:

- which `V71-C` handoffs are actually eligible for a bounded integration plan;
- what repository surface a ratified candidate may affect;
- how to distinguish proposed change, local trial, accepted diff, commit intent,
  merge truth, and released truth;
- how to require rollback readiness before any integration posture can be
  treated as safe;
- how to carry dissent, evidence gaps, scope limits, and non-authority
  guardrails into any trial plan;
- how to prevent a ratified candidate from becoming release, product, runtime,
  or dispatch authority just because a contained trial exists.

That work belongs in `V72`. It should make integration review explicit while
preserving the line between bounded review posture and actual merge / release
truth.

## Proposed Family Decomposition

`V72` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V72-A` | integration candidate containment plan, target boundary, and non-release guardrail over released `V71-C` handoffs |
| `V72-B` | contained integration trial record, effect-surface register, and rollback readiness |
| `V72-C` | commit/release authority posture boundary, post-integration outcome-review handoff, and family closeout alignment |

## Selected Surfaces For Future Starter Drafting

`V72-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_contained_integration_candidate_plan@1`
- `repo_integration_target_boundary@1`
- `repo_integration_non_release_guardrail@1`

Recommendation: select `V72-A` as the next default candidate after support
review integration, with `vNext+200` as the canonical starter bundle.

Later `V72` surfaces should remain support-layer until their own starter locks:

- `repo_contained_integration_trial_record@1`
- `repo_integration_effect_surface_register@1`
- `repo_integration_rollback_readiness@1`
- `repo_commit_release_authority_posture@1`
- `repo_post_integration_outcome_review_handoff@1`
- `repo_contained_integration_family_closeout_alignment@1`

Post-`V72-A` continuation posture: after `vNext+200` closes on `main`, select
`V72-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V72` family and does not
create a new next-arc-options selector version.

Post-`V72-B` continuation posture: after the `V72-B` slice closes on `main`,
select `V72-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V72` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- actual file edits for any candidate outside the future `V72` starter scope;
- autonomous commit, merge, or release authority;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation.

Those remain mapped future seams only until their own planning and lock surfaces
select them.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_CONTAINED_INTEGRATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_CONTAINED_INTEGRATION_REVIEW_V72_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json`
- `artifacts/agent_harness/v199/evidence_inputs/v71c_candidate_ratification_closeout_evidence_v199.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_ratification_amendment_scope_boundary_v199_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_candidate_ratification_family_closeout_alignment_v199_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis
  only, not lock authority.

## Lock Readiness Note

The future `vNext+200` starter lock should consume committed `V68`, `V69`,
`V70`, and `V71` closeouts, combined dogfood artifacts, `vNext+199` evidence
inputs, and released `V71-C` amendment-scope / post-ratification handoff
fixtures as concrete source rows. If any expected source is missing at lock
time, the `V72-A` containment plan should record that absence explicitly with
source-presence or source-status posture.

The lock should not reconstruct integration plans from prose memory, model
preference, operator vibe, or uncommitted transcript.

Before lock drafting, `V72-A` should preserve these planning constraints:

- only `V71-C` rows with `handoff_posture = ready_for_v72_review` may be
  eligible for contained integration planning;
- product pressure remains future-family routed;
- deferred or dissent-bearing candidates remain blocked unless a later lock
  explicitly selects settlement work;
- `V72-A` may implement its own schema/model/validator/test/fixture files under
  the active slice lock, but candidate contained-integration trial work remains
  unselected until a later `V72-B` lock;
- containment plans should embed or otherwise resolve through concrete
  `integration_source_rows`; source absence remains data, not prose memory;
- contained integration plan rows must distinguish target boundary, trial
  posture, rollback requirement, and non-release guardrail;
- `required_trial_posture` in `V72-A` is a later-trial requirement, not evidence
  that a trial already happened;
- target boundaries should use `target_resolution_kind` so `package_surface`
  cannot act as an unbounded target;
- eligible plans require a rollback requirement, but `V72-A` cannot claim
  rollback verification;
- no `V72-A` row may claim implementation has been performed.

## Recommended Next Drafting Move

Seek review over this `V72` planning/support bundle. After review patches, draft
the canonical `vNext+200` starter bundle for `V72-A` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS200.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS200.md`
- `docs/ASSESSMENT_vNEXT_PLUS200_EDGES.md`

The `vNext+200` lock should select containment-plan / target-boundary /
non-release-guardrail schema, validator, and reference-fixture work only. It
should not select trial execution, rollback settlement, commit/release posture,
outcome review, product projection, runtime permission, or dispatch.
