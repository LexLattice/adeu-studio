# Draft Next Arc Options v36

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`, refreshed after the
full internal `V46` family closed on `main`, after the imported
`adeu-edge-ledger-change-bundle` was normalized as support-only intake evidence rather
than live package, schema, or family authority, after `V53-B` closed on
`arc/v53-r4`, and now updated with `V53-C` closed on `arc/v53-r5`.

Authority layer: planning.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, the structural-reasoning assessment planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`, the repo self-description planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`, the applied benchmarking planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`, the authoritative normative markdown
planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`, the policy-to-taskpack and
worker-enforcement bridge planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`, the
semantic substrate planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`, the symbol
audit planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md`, the ODEU simulation
planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md`, or the paper semantics /
workbench planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`.

Instead, it records an eleventh connected candidate family:

how should ADEU internalize one repo-owned edge ledger / cumulative edge-space
accounting family downstream of released repo-description and symbol-audit surfaces,
without laundering the imported `adeu-edge-ledger-change-bundle` into precedent,
without silently promoting lexical test adjacency into proof, and without allowing
explicit override input to outrank applicability gates or drift outside the bound edge
frame?

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this planning draft, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V45-A` through `V45-F` are closed on `main` and now constitute the completed bounded
  repo self-description ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`.
- `V46-A` through `V46-E` are closed on `main` and now constitute the completed
  applied-benchmarking ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`.
- `V49-A` through `V49-D` are closed on `main` and now constitute the completed
  semantic substrate contract / recovery / lowering / bridge ladder recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`.
- `V50-A` through `V50-C` are closed on `main` and now constitute the completed symbol
  census / coverage / semantic-audit / session-helper ladder recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md`.
- `V51-A` through `V51-C` are closed on `main`.
- `V52-A` through `V52-D` are closed on `main`.
- `vNext+140` is the current implementation-arc baseline on `main`.
- `V53-A` is now closed on `arc/v53-r3`:
  - released `adeu_edge_class_catalog@1`
  - released `adeu_edge_probe_template_catalog@1`
  - released `adeu_symbol_edge_applicability_frame@1`
  - green PR CI on `#363`
  - targeted package checks only; no full local `make check` claim
- `V53-B` is now closed on `arc/v53-r4`:
  - released `adeu_symbol_edge_adjudication_ledger@1`
  - green PR CI on `#366`
  - targeted package checks passed with `21 passed`
  - attempted pre-merge `make check` hit then-pre-existing branch-baseline import-order
    lint, later repaired in the merged PR; no local passing `make check` claim is made
    here
- `V53-C` is now closed on `arc/v53-r5`:
  - released `adeu_edge_taxonomy_revision_register@1`
  - green PR CI on `#368`
  - targeted package checks passed with `34 passed`
  - focused review-fix rerun passed with `14 passed`
  - attempted local `make check` remained red in the same shared dedicated-worktree
    baseline cluster; no local passing `make check` claim is made here
- imported prototype bundles have now been normalized under
  `examples/external_prototypes/`, including:
  - `adeu-edge-ledger-change-bundle`
  - `adeu-history-semantics-bundle`
- the imported edge-ledger bundle is currently governed only as:
  - imported external `X2` bundle
  - `non_precedent`
  - intake-only today
- maintainer-side intake/alignment notes already exist for the edge-ledger bundle:
  - `examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md`
  - `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`

## Gap

The repo no longer lacks:

- one released descriptive repo baseline over `V45`;
- one released symbol census / coverage / semantic-audit / session stack over `V50`;
- one normalized intake pack that tells the truth about the external edge-ledger
  bundle and its blocker set.

The repo still lacks:

- one explicit bounded probe-strategy / test-intent integration seam after the core
  edge-ledger semantics are stable enough to consume it lawfully.

The next missing layer is therefore not merely more symbol audit, not a read-only
session helper extension, and not a reopening of closed taxonomy, adjudication, or
revision law.

The next missing layer is the `V53-D` bounded probe/test-intent integration lane
inside the already-instantiated ADEU edge ledger family.

## Relationship To `V45`, `V50`, And The Imported Bundle

`V45`, `V50`, the external-prototype intake notes, and this new candidate family are
connected but non-identical.

`V45` asks:

- what does the ADEU repo contain, and how are those surfaces typed and governed as a
  self-described artifact system?

`V50` asks:

- how should ADEU own one bounded read-only symbol census / coverage / semantic-audit /
  session family without silently forking the released descriptive baseline?

The external-prototype intake notes ask:

- how should imported bundles be preserved as evidence and normalized into repo-owned
  planning rather than treated as precedent-bearing overlays?

This new family asks:

- how should ADEU own one cumulative edge-space accounting family rather than only a
  heuristic downstream proto-package?
- how should edge taxonomy and applicability become repo-owned before stronger
  adjudication statuses are released?
- how should explicit override evidence be governed so it cannot outrank the
  applicability frame or silently drift outside it?
- how should `covered_by_existing_tests`-like and
  `bounded_safe_by_structure`-like statuses be weakened or strengthened so they do not
  overclaim what the evidence actually supports?
- how should revision move from one-off judgments toward an actual cumulative lineage /
  register surface?

`V53-A` should therefore be read as:

- package-first;
- taxonomy-first;
- applicability-first;
- explicit that it consumes the released `V45` / `V50` symbol-id and descriptive
  baseline rather than silently redefining them;
- explicit that starter scope should stop short of a fully promoted adjudication lane
  unless the override and evidence laws are already constitutional enough.

`V53-B` should therefore now be read as:

- later than `V53-A`;
- closed on `arc/v53-r4`;
- explicit adjudication-law hardening over the released taxonomy + applicability stack;
- explicit fail-closed override law;
- explicit evidence-semantics law for stronger statuses;
- explicit support-ref identity and input-order law for starter support fields;
- not a license to treat lexical adjacency as proof by default.

`V53-C` should therefore now be read as:

- later than closed `V53-A` and closed `V53-B`;
- closed on `arc/v53-r5`;
- one cumulative revision register / lineage lane only;
- explicit that split / merge / deprecate / stabilize history is now representable
  over time without minting live taxonomy mutation.

`V53-D` should therefore now be read as:

- later than the closed taxonomy, adjudication, and revision core slices;
- one bounded probe-strategy / test-intent integration seam only;
- explicit that later integration with released `V45-D` test-intent surfaces remains
  downstream of the now-closed revision-register core.

So this family may constrain:

- one repo-owned adjacent package for edge-space accounting;
- how released `V45` identity and `V50` descriptive artifacts are consumed downstream;
- how explicit edge evidence is typed and fail-closed;
- how later probe or reviewer helpers are prevented from laundering soft evidence into
  hard status.

But it may not mint:

- ambient continuation inside `V50`;
- silent promotion of the imported external package into precedent;
- a broad reviewer/mutation platform in the first slice;
- proof-level claims from lexical test adjacency alone; or
- override semantics that bypass applicability or frame membership.

Planning relationship:

- `V43` remains a valid connected candidate family from `v26`;
- `V44` remains a valid connected candidate family from `v27`, but its bounded ladder
  is already closed on `main`;
- `V45` remains a connected released family from `v28`;
- `V46` remains a connected released family from `v29`;
- `V47` remains a connected released family from `v30`;
- `V48` remains a connected released family from `v31`;
- `V49` remains a connected released family from `v32`;
- `V50` remains a connected released family from `v33`;
- `V51` remains a connected released family from `v34`;
- `V52` remains a connected released family from `v35`;
- this draft introduces an eleventh connected candidate family rather than widening
  `V50`.

## Recommended Family

- Family name: `V53`
- Family theme: ADEU edge ledger / cumulative edge-space accounting family
- Released earlier shaping inputs:
  - released `V45-A` through `V45-F`
  - released `V50-A` through `V50-C`
- Connected candidate families not reopened or superseded here:
  - `V43`
  - `V45`
  - `V50`
- Recommended support mapping reference:
  - `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`
- Recommended starter slice mapping reference:
  - `docs/DRAFT_ADEU_EDGE_LEDGER_V53C_IMPLEMENTATION_MAPPING_v0.md`
- Recommended next path for this branch:
  - `V53-D`
- Recommended next concrete arc for this branch if selected:
  - `vNext+147`
- Default path selection for this branch:
  - select `V53-D` as the next default candidate and current branch-local next path
    for `vNext+147` on `arc/v53-r5`

This family/path recommendation is branch-local to the `v36` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected planning
branches from `v26`, `v28`, and later module families remain in parallel scope.

## Suggested `V53` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V53-A` | taxonomy + applicability substrate | released `adeu_edge_class_catalog@1`, released `adeu_edge_probe_template_catalog@1`, and released `adeu_symbol_edge_applicability_frame@1` over one bounded pilot scope | closed on `arc/v53-r3` |
| `V53-B` | adjudication hardening lane | released `adeu_symbol_edge_adjudication_ledger@1` with fail-closed override law, explicit evidence semantics, and explicit support-ref identity/order law | closed on `arc/v53-r4` |
| `V53-C` | cumulative revision register lane | released revision lineage / register surface above isolated revision judgments | closed on `arc/v53-r5` |
| `V53-D` | bounded probe/test-intent integration lane | one explicit integration seam with later probe strategy or released `V45-D` test-intent surfaces only after the core ledger is stable | selected next path |

These output names are planning-level candidate names, not lock-level schema authority.

## Why This Path

- It treats the imported bundle as serious shaping evidence without laundering it into a
  live continuation of `V50`.
- It preserves the doctrinal boundary that descriptive `V50` artifacts remain upstream
  inputs while edge accounting becomes a distinct downstream family.
- It let the repo release the constant layer before the adjudication layer, and it kept
  the adjudication release bounded before revision/register widening.
- It now puts the strongest remaining blocker cluster in the right place:
  - cumulative revision history
  - later probe/test-intent integration
- It keeps probe execution and broader reviewer-platform semantics later.

## Candidate Package Ownership

The first planning pass should assume one primary family package:

- `packages/adeu_edge_ledger`

This package-ownership assumption is provisional and subordinate to a later family
decomposition or continuation lock.

It should be read as a planning convenience placeholder only, not as an implied
package-lock commitment.

## Governing References

The higher-order context notes for this family direction are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md`
- `docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md`
- `examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md`

Support-layer implementation mapping for this family direction:

- `docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md`

## Planning Boundary

- no reopening of released `V45` or released `V50` contracts is authorized by this
  planning draft;
- no lock-level schema authority is created by the candidate artifact names above;
- no adjudication status may overclaim proof solely because a lexical cue or test token
  matched;
- no override input may be assumed lawful by this planning draft; override law must be
  selected and locked explicitly later;
- no broad reviewer, mutation, or CI-enforcement platform is authorized by this
  planning draft;
- no ambient continuation of `V50` is selected by this planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v35.md",
  "baseline_arc": "vNext+143",
  "closed_prior_families": [
    "V45",
    "V46",
    "V50",
    "V51",
    "V52"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V45",
    "V50",
    "V53"
  ],
  "branch_candidate_family": "V53",
  "branch_candidate_status": "selected_for_v36_planning_surface_not_repo_wide_family_selection",
  "connected_families_not_reopened_here": [
    "V45",
    "V50"
  ],
  "closed_current_family_paths": [
    "V53-A",
    "V53-B"
  ],
  "planned_current_family_paths": [
    "V53-C",
    "V53-D"
  ],
  "default_next_arc_candidate_for_this_branch": "V53-C",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+145",
  "selected_current_family_path_for_this_branch": "V53-C",
  "selected_current_concrete_arc_for_this_branch": "vNext+145",
  "selected_current_path_branch": "arc/v53-r5",
  "selected_current_path_phase": "starter_draft",
  "family_architecture_doc": "not_selected_yet",
  "family_decomposition_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
  "support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
  "starter_slice_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53C_IMPLEMENTATION_MAPPING_v0.md",
  "planned_family_packages": [
    "packages/adeu_edge_ledger"
  ],
  "first_slice_active_packages": [
    "packages/adeu_edge_ledger"
  ],
  "family_theme": "adeu_edge_ledger_and_cumulative_edge_space_accounting",
  "external_bundle_intake_pack": "examples/external_prototypes/adeu-edge-ledger-change-bundle",
  "external_bundle_precedent_status": "non_precedent",
  "branch_local_planning_selection_only": true,
  "package_first_required": true,
  "starter_taxonomy_and_applicability_first_required": true,
  "starter_adjudication_may_be_deferred_until_override_law_is_constitutional": true,
  "released_v45_symbol_identity_must_be_consumed_not_redefined": true,
  "released_v50_descriptive_stack_must_be_consumed_not_reopened": true,
  "contradictory_override_input_must_fail_closed": true,
  "out_of_frame_override_input_must_fail_closed": true,
  "applicability_violating_override_input_must_fail_closed": true,
  "status_evidence_semantics_must_not_overclaim": true,
  "cumulative_revision_register_required_before_promotion": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```

`family_decomposition_doc` currently points to
`docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md` only as a
support-layer placeholder for the `V53` family. It is not architecture or
decomposition authority.

Historical-evidence note: the preserved first-draft planning copy intentionally
remains pre-repair, while the live planning baseline carries the repaired
`family_decomposition_doc` value. Baton
`artifacts/meta_loop/V53/V53-A/batons/006_arc_worker_starter_repair_claim.json`
remains the truth record for that repair.

Branch-local closeout note:

- `V53-A` is closed on `arc/v53-r3`
- `V53-B` is now closed on `arc/v53-r4`
- `V53-C` is now the selected starter-draft target on `arc/v53-r5`
- branch-local default next path remains `V53-C`
- branch-local default next concrete arc candidate remains `vNext+145`
## V53-D Starter Drafting Status (Step-3)

Status: in_progress on `arc/v53-r8`.

Starter drafting note:

- `V53-D` starter drafting is now in progress on `arc/v53-r8`.
- Targeted outputs are the four `vNEXT_PLUS147` starter docs plus the
  slice-specific `docs/DRAFT_ADEU_EDGE_LEDGER_V53D_IMPLEMENTATION_MAPPING_v0.md`.
- This remains starter drafting only and is not a released slice.
