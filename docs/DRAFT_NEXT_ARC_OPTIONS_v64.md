# Draft Next Arc Options v64

Status: planning handoff after `vNext+205` / `V73-C` merged on `main`, after
the `V73` family closeout pass, and after the combined `V68` through `V73`
dogfood probe.

Authority layer: planning.

This draft records the post-`V73` frontier. It does not authorize operator UI
implementation, product workbenching, product selection, runtime permission,
dispatch widening, external contest participation, release, or recursive
self-approval by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v63.md`, which selected the `V73` family. `vNext+203`,
`vNext+204`, and `vNext+205` then closed `V73-A`, `V73-B`, and `V73-C` without
creating additional family selector versions.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- latest closed implementation arc: `vNext+205`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v63.md`
- next planning obligation: select and review `V74` as the next family outside
  closed `V73`.

The combined `V68` / `V69` / `V70` / `V71` / `V72` / `V73` support dogfood
test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome entry / observation / regression / recommendation
  -> V74 operator projection pressure
```

## Next Planning Question

Now that a candidate can move through outcome review and produce source-bound
ledger, operator-cognition signal, and promotion / demotion recommendation rows
without adoption or release authority, should the next family be `V74`:
operator projection, typed case views, decision visibility, and product-facing
adjudication projection without authority minting?

## Recommended Next Pressure

- family: `V74`
- proposed family name:
  - `V74: operator projection, typed adjudication case views, decision
    visibility, and non-authority workbench posture`
- recommended planning posture:
  - select `V74` as the next family for support review;
  - treat `V74-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake as admitted candidate substrate;
  - consume `V70` review classification as evidence / gap substrate;
  - consume `V71` ratification and amendment-scope substrate;
  - consume `V72` contained integration and authority-posture substrate;
  - consume `V73` outcome ledger, operator-cognition signal, recommendation,
    and family closeout alignment as projection substrate;
  - project decision state to the operator without product authorization,
    runtime permission, dispatch, release, or recursive self-approval.

## Why `V74` Now

`V68` tells the repo where sources and authority boundaries sit. `V69` admits
candidate pressure without adoption. `V70` classifies evidence, adversarial
review, conflict, complementarity, gaps, and pre-ratification handoff. `V71`
records ratification, deferral, dissent, amendment scope, and
post-ratification handoff. `V72` records containment plans, trials, effects,
rollback readiness, and commit / release boundaries. `V73` records outcome
review, regression posture, tool-fitness drift, self-improvement ledger rows,
operator-cognition signals, and recommendations without self-approval.

The next bottleneck is operator projection:

- the operator now needs one governed view of the candidate state rather than
  scattered closeout, fixture, dogfood, and support artifacts;
- `V73-C` can recommend later review, including `v74_operator_projection_review`,
  but it cannot make that recommendation legible as an operator case;
- the typed-adjudication product wedge has been preserved as future-family
  pressure since `V69`, but it has not yet been represented as a governed case
  projection;
- model-output comparison and conceptual-diff artifacts can be useful only if
  their authority, evidence, ratification, outcome, and exception status remain
  visible;
- operator-facing views must show source gaps, blockers, and forbidden roles
  rather than smoothing them into product or implementation confidence.

That work belongs in `V74`. It should make ADEU decisions legible and
actionable for human review while preserving the line between projection and
authority.

## Proposed Family Decomposition

`V74` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V74-A` | operator projection case view, projection source index, and non-authority guardrail over released `V73-C` recommendation / ledger substrate |
| `V74-B` | typed adjudication case view, model-output comparison projection, and exception visibility register |
| `V74-C` | decision visibility contract, ratification-review workbench projection, post-projection handoff, and family closeout alignment |

## Selected Surfaces For Future Starter Drafting

`V74-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_operator_projection_case_view@1`
- `repo_operator_projection_source_index@1`
- `repo_operator_projection_non_authority_guardrail@1`

Recommendation: select `V74-A` as the next default candidate after support
review integration, with `vNext+206` as the canonical starter bundle.

Later `V74` surfaces should remain support-layer until their own starter locks:

- `repo_typed_adjudication_case_view@1`
- `repo_model_output_comparison_projection@1`
- `repo_projection_exception_visibility_register@1`
- `repo_decision_visibility_contract@1`
- `repo_ratification_review_workbench_projection@1`
- `repo_post_projection_handoff@1`
- `repo_operator_projection_family_closeout_alignment@1`

Post-`V74-A` continuation posture: after `vNext+206` closes on `main`, select
`V74-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V74` family and does not
create a new next-arc-options selector version.

Post-`V74-B` continuation posture: after the `V74-B` slice closes on `main`,
select `V74-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V74` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation;
- a live product UI or commercial product workbench;
- runtime permission or operator command execution;
- commit, PR update, merge, release, or released-truth authority;
- product authorization or product-market selection;
- autonomous recursive self-improvement approval;
- operator clicks, transcript turns, or visual prominence as authority;
- model-output comparison as benchmark truth or proof of superiority.

Those remain mapped future seams only until their own planning and lock
surfaces select them.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v63.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_OUTCOME_REVIEW_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`
- `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_OPERATOR_PROJECTION_V74_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v205/evidence_inputs/v73_family_closeout_alignment_v205.json`
- `artifacts/agent_harness/v205/evidence_inputs/v73c_candidate_outcome_closeout_evidence_v205.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_self_improvement_outcome_ledger_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_operator_cognition_outcome_signal_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_promotion_demotion_recommendation_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_review_family_closeout_alignment_v205_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+206` starter lock should consume committed `V68`, `V69`,
`V70`, `V71`, `V72`, and `V73` closeouts, combined dogfood artifacts,
`vNext+205` evidence inputs, and released `V73-C` ledger / operator-signal /
recommendation / family closeout fixtures as concrete source rows. If any
expected source is missing at lock time, the `V74-A` projection surface should
record that absence explicitly with source-presence or source-status posture.

The lock should not reconstruct projection state from prose memory, model
preference, operator vibe, or uncommitted transcript.

Before lock drafting, `V74-A` should preserve these planning constraints:

- only released `V73-C` recommendation / ledger substrate may be projected as
  an operator case;
- `V74-A` may create case-view rows, projection source rows, visible status
  rows, visible blocker / exception-summary rows inside the case-view payload,
  projection-horizon rows, visible-authority-state rows, and boundary
  guardrails only;
- `V74-A` must not implement a live product UI, product workbench, command
  surface, dispatch loop, ratification action, release action, or runtime
  permission surface;
- every projected case must make its authority boundary visible;
- product-pressure cases must carry `product_authority_required` or equivalent
  later-authority posture unless explicitly rejected or out of scope;
- missing sources, blockers, unresolved regressions, dissent, and later
  authority requirements must remain visible rather than being smoothed into
  a positive product or implementation story.

## Recommended Next Drafting Move

Review this selector together with the `V74` architecture and `A` / `B` / `C`
support implementation specs. After review patches are integrated, draft the
canonical `V74-A` starter trio:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS206.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS206.md`
- `docs/ASSESSMENT_vNEXT_PLUS206_EDGES.md`

The `vNext+206` lock should select `V74-A` only.
