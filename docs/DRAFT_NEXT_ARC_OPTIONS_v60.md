# Draft Next Arc Options v60

Status: planning handoff after `vNext+193` / `V69-C` merged on `main` and after
the `V69` family closeout pass.

Authority layer: planning.

This draft records the post-`V69` frontier. It does not authorize implementation,
candidate adoption, evidence settlement, ratification, integration, product
projection, commit / merge / release authority, runtime permission, or dispatch
widening by itself.

## Selector Versioning Correction

This draft restores the intended selector discipline:

- `DRAFT_NEXT_ARC_OPTIONS_v*` should advance once per family-level selection;
- sub-lanes inside an already selected family should advance through
  `vNext+<n>` starter / implementation / closeout bundles, not through new
  `DRAFT_NEXT_ARC_OPTIONS_v*` files;
- `V70-B` and `V70-C` should not receive their own next-arc-options drafts unless
  the family boundary materially changes and a maintainer explicitly records that
  exception.

Recent lane-level selector handoffs such as `DRAFT_NEXT_ARC_OPTIONS_v58.md` and
`DRAFT_NEXT_ARC_OPTIONS_v59.md` are historical continuity artifacts, not the
precedent-bearing workflow. The current family-level predecessor for this `V70`
selector is `DRAFT_NEXT_ARC_OPTIONS_v57.md`, which selected the `V69` family.

## Current Frontier

- `V67` is closed on `main`.
- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- latest closed implementation arc: `vNext+193`
- latest next-arc-options file before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v59.md`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v57.md`
- next planning obligation: select and review `V70` as the next family outside
  closed `V69`.

The combined `V68` / `V69` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.json`

That support result says `V69` correctly preserves post-`V68` candidate pressure
as explicit gap / handoff posture rather than laundering it into `V68`
cartography authority.

## Next Planning Question

Now that candidate pressure can be mapped, admitted, derived, gap-scanned, bound
to operator / workflow residue, and handed off without adoption, should the next
family be `V70`: candidate evidence classification, adversarial review
classification, and pre-ratification handoff?

## Recommended Next Pressure

- family: `V70`
- proposed family name:
  - `V70: candidate evidence classification, adversarial review classification,
    and pre-ratification handoff`
- recommended planning posture:
  - select `V70` as the next family for support review;
  - treat `V70-A` as the only immediate future starter target after review;
  - consume `V68` cartography as source / authority substrate;
  - consume `V69` candidate intake, derivation, gap, operator/residue, and
    pre-`V70` handoff surfaces as candidate substrate;
  - classify evidence and adversarial-review needs without ratifying,
    implementing, releasing, productizing, or dispatching any candidate.

## Why `V70` Now

`V68` tells the repo where the relevant arc, source, evidence, and authority
surfaces sit. `V69` admits candidate pressure into typed, source-bound,
non-adoptive records.

The next bottleneck is not more intake. It is review classification:

- what evidence is present;
- what evidence is missing or stale;
- which ODEU lane or lanes a claim pressures;
- which evidence is not actually evidence;
- which candidates require adversarial review;
- which conflicts or complementarities shape later ratification review;
- which candidates can be handed to `V71` for ratification review without being
  ratified by `V70`.

That work belongs in `V70`. It should make candidate review state explicit while
preserving the line between classification and settlement.

## Proposed Family Decomposition

`V70` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V70-A` | evidence classification backbone: evidence-source index, candidate claim classification, and review-boundary guardrails |
| `V70-B` | adversarial review matrix, review relation and conflict register, and review gap scan |
| `V70-C` | classification synthesis, pre-`V71` handoff, and family closeout hardening |

## Selected Surfaces For Future Starter Drafting

`V70-A` should be the first active slice after support review. Candidate starter
surfaces:

- `repo_candidate_evidence_classification_record@1`
- `repo_candidate_evidence_source_index@1`
- `repo_candidate_review_boundary_guardrail@1`

Recommendation: select `V70-A` as the next default candidate after support
review integration, with `vNext+194` as the canonical starter bundle.

Later `V70` surfaces should remain support-layer until their own starter locks:

- `repo_candidate_adversarial_review_matrix@1`
- `repo_candidate_review_conflict_register@1`
- `repo_candidate_review_gap_scan@1`
- `repo_candidate_review_classification_summary@1`
- `repo_candidate_pre_ratification_handoff@1`

## Non-Selection

This selector handoff does not select:

- `V71` ratification;
- `V72` contained integration or commit/release posture;
- `V73` outcome review;
- `V74` operator/product projection;
- `V75` dispatch or multi-worker orchestration;
- `V43` external-world contest participation.

Those remain mapped future seams only until their own planning and lock surfaces
select them.

## Inputs For Support Review

Primary inputs:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v59.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.json`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_CANDIDATE_REVIEW_CLASSIFICATION_V70_PLANNING_v0.md`
- `artifacts/agent_harness/v193/evidence_inputs/v69_family_closeout_alignment_v193.json`
- `artifacts/agent_harness/v193/evidence_inputs/v69c_recursive_candidate_intake_handoff_evidence_v193.json`

Support / process companion:

- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`, support/process synthesis
  only, not lock authority.

## Lock Readiness Note

The future `vNext+194` starter lock should consume committed `V68` / `V69`
closeouts, combined dogfood artifacts, `vNext+193` evidence inputs, and the
released `V69-C` pre-`V70` handoff fixture as concrete source rows. If any
expected source is missing at lock time, the `V70-A` source index should record
that absence explicitly with a source-presence posture such as:

- `present`
- `missing_expected_support_artifact`
- `not_uploaded_in_review_snapshot`
- `generated_later`
- `external_unavailable`

The lock should not reconstruct handoff or evidence state from prose memory.

## Recommended Next Drafting Move

Seek review over this `V70` planning/support bundle. After review patches, draft
the canonical `vNext+194` starter bundle for `V70-A` only:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS194.md`
- `docs/ASSESSMENT_vNEXT_PLUS194_EDGES.md`

The `vNext+194` lock should select evidence classification schema / validator /
fixture work only. It should not select adversarial settlement, `V71`
ratification, integration, product projection, release authority, or dispatch.
