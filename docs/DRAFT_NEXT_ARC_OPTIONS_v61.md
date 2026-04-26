# Draft Next Arc Options v61

Status: planning handoff after `vNext+196` / `V70-C` merged on `main` and after
the `V70` family closeout pass.

Authority layer: planning.

This draft records the post-`V70` frontier. It does not authorize
implementation, contained integration, product projection, commit / merge /
release authority, runtime permission, dispatch widening, or external contest
participation by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v60.md`, which selected the `V70` family. `vNext+194`,
`vNext+195`, and `vNext+196` then closed `V70-A`, `V70-B`, and `V70-C` without
creating additional family selector versions.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- latest closed implementation arc: `vNext+196`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v60.md`
- next planning obligation: select and review `V71` as the next family outside
  closed `V70`.

The combined `V68` / `V69` / `V70` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended:

```text
V68 map substrate
  -> V69 source-bound candidate pressure
  -> V70 evidence / adversarial / gap classification
  -> V70 pre-ratification handoff
  -> V71 ratification-review pressure
```

## Next Planning Question

Now that candidate pressure can be mapped, admitted, derived, reviewed,
gap-scanned, summarized, and handed off without adoption, should the next family
be `V71`: candidate ratification review, settlement, amendment-scope boundary,
and human-internal authority profile?

## Recommended Next Pressure

- family: `V71`
- proposed family name:
  - `V71: candidate ratification review, settlement, amendment-scope boundary,
    and human-internal authority profile`
- recommended planning posture:
  - select `V71` as the next family for support review;
  - treat `V71-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake as admitted candidate substrate;
  - consume `V70` classification, adversarial review, relation, gap, summary,
    and pre-ratification handoff surfaces as review substrate;
  - ratify, reject, defer, or settle candidate review posture without beginning
    implementation, integration, release, product projection, runtime
    permission, or dispatch.

## Why `V71` Now

`V68` tells the repo where sources and authority boundaries sit. `V69` admits
candidate pressure without adoption. `V70` classifies evidence, adversarial
review, conflict, complementarity, gaps, and pre-ratification handoff.

The next bottleneck is ratification review:

- which `V70-C` handoffs are eligible for ratification review;
- which handoffs require conflict settlement before any ratification posture;
- which candidates should be rejected, deferred, or sent to future-family
  review;
- which authority actor or profile is allowed to ratify a candidate inside the
  repo harness;
- what amendment scope a ratified candidate actually permits;
- how warning-only review signals differ from gating blockers;
- how to prevent ratification from laundering itself into implementation or
  release authority.

That work belongs in `V71`. It should make ratification explicit while
preserving the line between ratification and downstream integration.

## Proposed Family Decomposition

`V71` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V71-A` | ratification request, authority-profile, and scope-boundary backbone over released `V70-C` handoffs |
| `V71-B` | settlement and ratification records over ready, blocked, deferred, or rejected candidates |
| `V71-C` | amendment-scope hardening, post-ratification handoff, and family closeout alignment |

## Selected Surfaces For Future Starter Drafting

`V71-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_candidate_ratification_request@1`
- `repo_ratification_authority_profile@1`
- `repo_ratification_request_scope_boundary@1`

Recommendation: select `V71-A` as the next default candidate after support
review integration, with `vNext+197` as the canonical starter bundle.

Later `V71` surfaces should remain support-layer until their own starter locks:

- `repo_candidate_ratification_record@1`
- `repo_review_settlement_record@1`
- `repo_ratification_dissent_register@1`
- `repo_ratification_amendment_scope_boundary@1`
- `repo_post_ratification_handoff@1`

Post-`V71-A` continuation posture: after `vNext+197` closes on `main`, select `V71-B` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V71` family and does not
create a new next-arc-options selector version.

Post-`V71-B` continuation posture: after the `V71-B` slice closes on `main`, select `V71-C` as the next default candidate for the next canonical starter bundle.
That selection remains inside the already selected `V71` family and does not
create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- `V72` contained integration, commit/release posture, or rollback;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation.

Those remain mapped future seams only until their own planning and lock surfaces
select them.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_CANDIDATE_RATIFICATION_REVIEW_V71_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_COMBINED_DOGFOOD_TEST_v0.json`
- `artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json`
- `artifacts/agent_harness/v196/evidence_inputs/v70c_candidate_review_summary_handoff_evidence_v196.json`
- `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis
  only, not lock authority.

## Lock Readiness Note

The future `vNext+197` starter lock should consume committed `V68`, `V69`, and
`V70` closeouts, combined dogfood artifacts, `vNext+196` evidence inputs, and
the released `V70-C` summary / pre-ratification handoff fixtures as concrete
source rows. If any expected source is missing at lock time, the `V71-A` request
or authority profile should record that absence explicitly with source-presence
or source-status posture.

The lock should not reconstruct ratification requests from prose memory, model
preference, operator vibe, or uncommitted transcript.

Before lock drafting, `V71-A` should also preserve the review patches from
`REVIEW_GPTPRO_CANDIDATE_RATIFICATION_REVIEW_V71_PLANNING_v0.md`:

- explicit ratification source rows;
- authority actor kind separated from authority grant source kind;
- request-scope boundary distinct from later amendment scope;
- warning-only review signals separated from gating blockers;
- no final ratification outcome or next-surface routing inside `V71-A`.

## Recommended Next Drafting Move

Seek review over this `V71` planning/support bundle. After review patches, draft
the canonical `vNext+197` starter bundle for `V71-A` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md`
- `docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md`

The `vNext+197` lock should select ratification request / authority-profile /
scope-boundary schema, validator, and reference-fixture work only. It should not
select settlement records, post-ratification handoff, implementation,
integration, product projection, release authority, runtime permission, or
dispatch.
