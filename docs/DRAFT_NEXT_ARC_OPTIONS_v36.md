# Draft Next Arc Options v36

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md`, refreshed after the
full internal `V46` family closed on `main`, and after the imported
`adeu-edge-ledger-change-bundle` was normalized as support-only intake evidence rather
than live package, schema, or family authority.

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

- one repo-owned edge taxonomy package that treats edge-space accounting as a distinct
  family rather than as an ambient extension of `adeu_symbol_audit`;
- one typed applicability frame over the released `V50` stack that can say:
  - `applicable`
  - `not_applicable`
  - `underdetermined`
  without yet overclaiming adjudication;
- one explicit adjudication lane with constitutional fail-closed rules for:
  - contradictory overrides
  - out-of-frame overrides
  - applicability-violating overrides;
- one explicit evidence-law boundary between:
  - lexical test adjacency
  - structural-safety inference
  - explicit witness / checked-no-witness evidence;
- one cumulative revision register / lineage posture rather than only one-off taxonomy
  revision judgments.

The missing layer is therefore not merely more symbol audit, not a read-only session
helper extension, and not yet a probe-execution or mutation platform.

The missing layer is an ADEU edge ledger family.

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

`V53-B` should therefore be read as:

- later than `V53-A`;
- explicit adjudication-law hardening over the released taxonomy + applicability stack;
- explicit fail-closed override law;
- explicit evidence-semantics law for stronger statuses;
- not a license to treat lexical adjacency as proof by default.

`V53-C` should therefore be read as:

- later than released `V53-A` and `V53-B`;
- one cumulative revision register / lineage lane only;
- explicit that split / merge / deprecate / stabilize history must be representable
  over time, not only through isolated revision judgments.

`V53-D` should therefore be read as:

- later than the taxonomy, adjudication, and revision core slices;
- one bounded probe-strategy / test-intent integration seam only;
- explicit that later integration with released `V45-D` test-intent surfaces remains
  deferred until the edge ledger itself is stable enough to consume them lawfully.

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
- Recommended next path for this branch:
  - `V53-A`
- Recommended next concrete arc for this branch if selected:
  - `vNext+141_placeholder`
- Default path selection for this branch:
  - select `V53-A` as the next default candidate

This family/path recommendation is branch-local to the `v36` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected planning
branches from `v26`, `v28`, and later module families remain in parallel scope.

## Suggested `V53` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V53-A` | taxonomy + applicability substrate | released `adeu_edge_class_catalog@1`, released `adeu_edge_probe_template_catalog@1`, and released `adeu_symbol_edge_applicability_frame@1` over one bounded pilot scope | planned |
| `V53-B` | adjudication hardening lane | released `adeu_symbol_edge_adjudication_ledger@1` with fail-closed override law and explicit evidence semantics | planned |
| `V53-C` | cumulative revision register lane | released revision lineage / register surface above isolated revision judgments | planned |
| `V53-D` | bounded probe/test-intent integration lane | one explicit integration seam with later probe strategy or released `V45-D` test-intent surfaces only after the core ledger is stable | planned |

These output names are planning-level candidate names, not lock-level schema authority.

## Why This Path

- It treats the imported bundle as serious shaping evidence without laundering it into a
  live continuation of `V50`.
- It preserves the doctrinal boundary that descriptive `V50` artifacts remain upstream
  inputs while edge accounting becomes a distinct downstream family.
- It lets the repo release the constant layer before the overclaimed adjudication layer.
- It puts the strongest blocker cluster in the right place:
  - override constitutionality
  - evidence/status semantics
  - cumulative revision history
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
  "baseline_arc": "vNext+140",
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
  "closed_current_family_paths": [],
  "planned_current_family_paths": [
    "V53-A",
    "V53-B",
    "V53-C",
    "V53-D"
  ],
  "default_next_arc_candidate_for_this_branch": "V53-A",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+141_placeholder",
  "family_architecture_doc": "not_selected_yet",
  "family_decomposition_doc": "not_selected_yet",
  "support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
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
