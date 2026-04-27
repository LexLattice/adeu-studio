# Draft Next Arc Options v63

Status: planning handoff after `vNext+202` / `V72-C` merged on `main`, after
the `V72` family closeout pass, and after the combined `V68` through `V72`
dogfood probe.

Authority layer: planning.

This draft records the post-`V72` frontier. It does not authorize outcome
review implementation, promotion, demotion, adoption, release, product
projection, runtime permission, dispatch widening, or external contest
participation by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v62.md`, which selected the `V72` family. `vNext+200`,
`vNext+201`, and `vNext+202` then closed `V72-A`, `V72-B`, and `V72-C` without
creating additional family selector versions.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- latest closed implementation arc: `vNext+202`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v62.md`
- next planning obligation: select and review `V73` as the next family outside
  closed `V72`.

The combined `V68` / `V69` / `V70` / `V71` / `V72` support dogfood test is
recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome-review pressure
```

## Next Planning Question

Now that a candidate can move from mapped source substrate through intake,
review, ratification, contained integration planning, trial/effect/rollback
records, and commit/release authority posture without becoming release truth,
should the next family be `V73`: candidate outcome review, regression
tracking, tool-fitness drift, and post-outcome recommendation?

## Recommended Next Pressure

- family: `V73`
- proposed family name:
  - `V73: candidate outcome review, regression ledger, tool-fitness drift, and
    post-outcome recommendation`
- recommended planning posture:
  - select `V73` as the next family for support review;
  - treat `V73-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake as admitted candidate substrate;
  - consume `V70` review classification as evidence / gap substrate;
  - consume `V71` ratification and amendment-scope substrate;
  - consume `V72` contained integration trial / effect / rollback /
    authority-posture substrate;
  - record outcome-review evidence and boundaries without promoting,
    demoting, adopting, releasing, productizing, dispatching, or claiming
    self-improvement success.

## Why `V73` Now

`V68` tells the repo where sources and authority boundaries sit. `V69` admits
candidate pressure without adoption. `V70` classifies evidence, adversarial
review, conflict, complementarity, gaps, and pre-ratification handoff. `V71`
records ratification, deferral, dissent, amendment scope, and post-ratification
handoff. `V72` records containment plans, bounded trial posture, effect
surfaces, rollback readiness, and commit / release authority boundaries without
release truth.

The next bottleneck is outcome review:

- which `V72-C` handoffs are eligible for outcome review;
- what baseline / intervention / evaluation horizon should be inspected;
- what counts as outcome evidence versus trial evidence, review evidence, or
  authority posture;
- whether the trial helped, harmed, regressed, drifted, or remains
  inconclusive;
- whether tool fitness changed or stale tool assumptions were exposed;
- whether the operator-cognition / workflow-residue signal is real enough to
  preserve for later projection;
- how to produce promotion, demotion, repeat, or deferral recommendations
  without self-approval.

That work belongs in `V73`. It should make outcome review explicit while
preserving the line between review/recommendation and adoption, release,
product, runtime, or dispatch authority.

## Proposed Family Decomposition

`V73` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V73-A` | outcome-review entry, outcome evidence source index, and non-promotion guardrail over released `V72-C` handoffs |
| `V73-B` | outcome observation records, regression register, and tool-fitness drift register |
| `V73-C` | self-improvement outcome ledger, operator-cognition outcome signal, promotion/demotion recommendation, and family closeout alignment |

## Selected Surfaces For Future Starter Drafting

`V73-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_candidate_outcome_review_entry@1`
- `repo_outcome_evidence_source_index@1`
- `repo_outcome_review_boundary_guardrail@1`

Recommendation: select `V73-A` as the next default candidate after support
review integration, with `vNext+203` as the canonical starter bundle.

Later `V73` surfaces should remain support-layer until their own starter locks:

- `repo_candidate_outcome_observation_record@1`
- `repo_outcome_regression_register@1`
- `repo_tool_fitness_drift_register@1`
- `repo_self_improvement_outcome_ledger@1`
- `repo_operator_cognition_outcome_signal@1`
- `repo_outcome_promotion_demotion_recommendation@1`
- `repo_outcome_review_family_closeout_alignment@1`

Post-`V73-A` continuation posture: after `vNext+203` closes on `main`, select `V73-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V73` family and does not
create a new next-arc-options selector version.

Post-`V73-B` continuation posture: after the `V73-B` slice closes on `main`,
select `V73-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V73` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation;
- promotion or demotion as final adoption authority;
- commit, PR update, merge, release, or released-truth authority;
- product authorization, runtime permission, or dispatch authority;
- autonomous recursive self-improvement approval;
- model-output benchmark claims as proof of self-improvement.

Those remain mapped future seams only until their own planning and lock surfaces
select them.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v62.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CONTAINED_INTEGRATION_REVIEW_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_OUTCOME_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v202/evidence_inputs/v72_family_closeout_alignment_v202.json`
- `artifacts/agent_harness/v202/evidence_inputs/v72c_contained_integration_closeout_evidence_v202.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_commit_release_authority_posture_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_post_integration_outcome_review_handoff_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_contained_integration_family_closeout_alignment_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+203` starter lock should consume committed `V68`, `V69`,
`V70`, `V71`, and `V72` closeouts, combined dogfood artifacts, `vNext+202`
evidence inputs, and released `V72-C` authority-posture / post-integration
handoff / family closeout fixtures as concrete source rows. If any expected
source is missing at lock time, the `V73-A` entry surface should record that
absence explicitly with source-presence or source-status posture.

The lock should not reconstruct outcome posture from prose memory, model
preference, operator vibe, or uncommitted transcript.

Before lock drafting, `V73-A` should preserve these planning constraints:

- only `V72-C` rows with `handoff_posture = ready_for_v73_review` may be
  eligible for outcome-review entry;
- `V73-A` may create review entries, evidence-source index rows, baseline /
  intervention / evaluation horizon rows, and boundary guardrails only;
- `V73-A` must not classify outcome success, regression, tool drift, or
  promotion / demotion;
- product pressure remains future-family routed;
- release, product, runtime, dispatch, and external contest authority remain
  forbidden downstream roles;
- outcome evidence source rows must distinguish trial evidence, observed
  effect evidence, rollback evidence, authority-posture evidence, dogfood
  evidence, and operator-cognition evidence, and must also distinguish the
  source's evidence role so context sources cannot become outcome proof;
- eligible outcome-review entries must reference first-class baseline,
  intervention, and evaluation horizon rows;
- blocked outcome-review entries should carry machine-checkable blocker refs
  rather than relying only on prose limitation notes;
- missing baseline or evaluation evidence must be represented as explicit
  source posture, not source-free memory;
- `V73-A` may implement its own schema/model/validator/test/fixture files under
  the active slice lock, but it must not perform outcome judgment;
- the first `V73-A` fixture should remain entry-only: no `benefit_observed`,
  regression judgment, tool-fitness drift judgment, ledger row, or
  promotion/demotion recommendation.

## Recommended Next Drafting Move

Seek review over this `V73` planning/support bundle. After review patches,
draft the canonical `vNext+203` starter bundle for `V73-A` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS203.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS203.md`
- `docs/ASSESSMENT_vNEXT_PLUS203_EDGES.md`

The `vNext+203` lock should select outcome-review-entry / evidence-source-index
/ boundary-guardrail schema, validator, and reference-fixture work only. It
should not select outcome observation, regression classification, tool-fitness
drift, promotion/demotion recommendation, product projection, runtime
permission, or dispatch.
