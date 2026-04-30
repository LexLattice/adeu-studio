# Draft Next Arc Options v65

Status: planning handoff after `vNext+208` / `V74-C` merged on `main`, after
the `V74` family closeout pass, after the combined `V68` through `V74`
dogfood probe, and after the post-`V74` multi-arc roadmap draft.

Authority layer: planning.

This draft records the post-`V74` frontier. It does not authorize dispatch,
worker assignment, command execution, runtime permission, product authorization,
external contest participation, commit, PR update, merge, release, benchmark
truth, global model selection, or recursive self-approval by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v64.md`, which selected the `V74` family. `vNext+206`,
`vNext+207`, and `vNext+208` then closed `V74-A`, `V74-B`, and `V74-C`
without creating additional family selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- latest closed implementation arc: `vNext+208`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v64.md`
- next planning obligation: select and review `V75` as the next family outside
  closed `V74`.

The combined `V68` through `V74` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 request / settlement / ratification-review / handoff
  -> V72 containment plan / trial / effect / rollback / authority posture
  -> V73 outcome entry / observation / regression / tool-fitness / ledger
  -> V74 operator projection / typed case view / comparison / visibility / handoff
  -> V75 dispatch / orchestration pressure
```

## Next Planning Question

Now that a candidate can move through operator projection, typed case view,
model-output comparison projection, exception visibility, decision visibility,
ratification-review workbench projection, and post-projection handoff without
minting authority, should the next family be `V75`: dispatch-review,
multi-worker orchestration posture, worker-output reconciliation planning, and
non-execution guardrails?

## Recommended Next Pressure

- family: `V75`
- proposed family name:
  - `V75: dispatch-review, multi-worker orchestration posture,
    worker-output reconciliation planning, and non-execution guardrails`
- recommended planning posture:
  - select `V75` as the next family for support review;
  - treat `V75-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake as admitted candidate substrate;
  - consume `V70` review classification as evidence / gap substrate;
  - consume `V71` ratification and amendment-scope substrate;
  - consume `V72` contained integration and authority-posture substrate;
  - consume `V73` outcome ledger and recommendation substrate;
  - consume `V74` operator projection, visibility contract, workbench
    projection, exception, and post-projection handoff substrate;
  - represent dispatch-review pressure without dispatch, worker execution,
    runtime permission, product authority, release, external contest
    participation, or recursive self-approval.

## Why `V75` Now

`V74-C` produced `repo_post_projection_handoff@1` rows that can request later
`v75_dispatch_review` while carrying decision visibility contracts, workbench
projection rows, exceptions, required later authority, and non-dispatch
guardrails.

The next bottleneck is not another operator-facing projection. The next
bottleneck is making dispatch pressure governable before any runtime or worker
widening happens:

- which projected cases are eligible for dispatch review;
- which sources and authority requirements make that pressure legitimate;
- which exceptions or blockers prevent orchestration planning;
- which worker roles would be needed if a later authority selected dispatch;
- what IO and tool-applicability contracts would constrain those workers;
- how projected or later-observed worker outputs would be reconciled;
- which later family should review runtime, product, external, or experiment
  pressure without treating `V75` as execution.

That work belongs in `V75`. It should make dispatch review typed and auditable
while preserving the line between review posture and action.

## Proposed Family Decomposition

`V75` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V75-A` | dispatch-review request, dispatch source index, and non-execution guardrail over released `V74-C` post-projection handoff / visibility substrate |
| `V75-B` | worker role capacity profiles, multi-worker assignment plans, worker IO contracts, worker tool-applicability matrix, and dispatch exception register |
| `V75-C` | worker-output reconciliation plan, dispatch reconciliation contract, post-dispatch-review handoff, and dispatch-review family closeout alignment |

## Selected Surfaces For Future Starter Drafting

`V75-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_dispatch_review_request@1`
- `repo_dispatch_source_index@1`
- `repo_dispatch_non_execution_guardrail@1`

Recommendation: select `V75-A` as the next default candidate after support
review integration, with `vNext+209` as the canonical starter bundle if no
intervening arc claims that number.

Later `V75` surfaces should remain support-layer until their own starter locks:

- `repo_worker_role_capacity_profile@1`
- `repo_multi_worker_assignment_plan@1`
- `repo_worker_io_contract@1`
- `repo_worker_tool_applicability_matrix@1`
- `repo_dispatch_exception_register@1`
- `repo_worker_output_reconciliation_plan@1`
- `repo_dispatch_reconciliation_contract@1`
- `repo_post_dispatch_review_handoff@1`
- `repo_dispatch_review_family_closeout_alignment@1`

Post-`V75-A` continuation posture: after `vNext+209` closes on `main`, select
`V75-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V75` family and does not
create a new next-arc-options selector version.

Post-`V75-B` continuation posture: after the `V75-B` slice closes on `main`,
select `V75-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V75` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- runtime command execution;
- actual worker assignment or dispatch;
- product launch, product-market validation, or product authorization;
- external contest participation or `V43` activation;
- commit, PR update, merge, release, or released-truth authority;
- recursive policy amendment;
- global model selection;
- benchmark truth;
- runtime permission or command preflight authority;
- living memory / graph authority.

Those remain mapped future seams only until their own planning and lock
surfaces select them.

## Entry And Non-Entry Criteria

`V75` is selector-ready because the post-`V74` substrate can cite concrete
released `V74-C` rows showing:

- at least one `repo_post_projection_handoff@1` row carrying
  `v75_dispatch_review` or equivalent later-dispatch-review pressure;
- a decision visibility contract for the case;
- a ratification-review workbench projection row that permits review-only
  operator action;
- visible carried exceptions, or an explicit checked absence of carried
  exceptions;
- required later authority rows for runtime, product, release, external, or
  dispatch-sensitive action;
- non-dispatch / non-execution guardrails.

Roadmap and support-review documents may contextualize this selection, but they
are not sufficient eligibility sources for `eligible_for_dispatch_review`.
Eligibility requires concrete released `V74-C` substrate: post-projection
handoff, decision visibility contract, workbench projection, visible exceptions
or checked absence, required later authority, and non-dispatch /
non-execution guardrails.

`V75` must not be used if the only evidence is:

- operator desire to "turn on agents";
- a model suggestion without source-bound `V74-C` handoff;
- an unresolved product-authority gap being smuggled in as dispatch pressure;
- an external contest objective without `V43` / external-world branch posture;
- a runtime command request without a later runtime permission surface;
- a worker-output comparison that lacks model-output provenance or
  benchmark-truth guardrails.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_POST_V74_MULTI_ARC_ROADMAP_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_DISPATCH_REVIEW_V75_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v208/evidence_inputs/v74_family_closeout_alignment_v208.json`
- `artifacts/agent_harness/v208/evidence_inputs/v74c_operator_projection_closeout_evidence_v208.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_decision_visibility_contract_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_ratification_review_workbench_projection_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_post_projection_handoff_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_operator_projection_family_closeout_alignment_v208_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis only,
  not lock authority.

## Lock Readiness Note

The future `vNext+209` starter lock should consume committed `V68` through
`V74` closeouts, the combined dogfood artifacts, `vNext+208` evidence inputs,
and released `V74-C` visibility / workbench / handoff / closeout fixtures as
concrete source rows. If any expected source is missing at lock time, the
`V75-A` dispatch-review surface should record that absence explicitly with
source-presence or source-status posture.

The lock should not reconstruct dispatch-review state from prose memory, model
preference, operator vibe, or uncommitted transcript.

Before lock drafting, `V75-A` should preserve these planning constraints:

- only released `V74-C` post-projection handoff and visibility substrate may be
  promoted into a dispatch-review request;
- `V75-A` may create dispatch-review request rows, dispatch source rows, and
  non-execution guardrail rows only;
- `V75-A` must not implement worker assignment, command execution, runtime
  permission, product authorization, PR, merge, release, external contest
  participation, or recursive policy amendment;
- every dispatch-review request must make required later authority and
  non-execution guardrails visible;
- product pressure, external branch pressure, runtime command pressure, and
  unresolved exceptions must stay blocked or future-family-only unless a later
  authority surface selects them.

Name hygiene: the `V75` bundle intentionally supersedes earlier roadmap
placeholder names that could imply execution or observed outputs. Use
`repo_worker_output_reconciliation_plan@1` rather than
`repo_worker_output_reconciliation_record@1`, and use
`repo_post_dispatch_review_handoff@1` rather than
`repo_post_dispatch_outcome_review_handoff@1`.

## Recommended Next Drafting Move

Review this selector together with the `V75` architecture and `A` / `B` / `C`
support implementation specs. After review patches are integrated, draft the
canonical `V75-A` starter trio:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS209.md`
- `docs/ASSESSMENT_vNEXT_PLUS209_EDGES.md`

The `vNext+209` lock should select `V75-A` only.
