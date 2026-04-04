# Draft Next Arc Options v32

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`, updated after the
bounded `V48` family closed on `main`, the imported GPT Pro prototype bundles were
normalized into repo-owned intake packs plus maintainer-side moduleization planning,
and the bounded `V49-A` semantic substrate contract slice, bounded `V49-B` semantic
recovery slice, bounded `V49-C` deterministic lowering slice, and bounded `V49-D`
semantic-seed bridge slice closed on `main`, completing the bounded `V49` family with
no further internal `V49` path currently selected.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, the structural-reasoning assessment planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`, the repo self-description planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`, the applied benchmarking planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`, the authoritative normative markdown
planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`, or the policy-to-taskpack and
worker-enforcement bridge planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`.

It also does not replace the support/planning posture of:

- `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`

Instead, it records a seventh connected candidate family and the first real
implementation-family move grounded in those support notes:

how should ADEU internalize canonical semantic language / syntax-of-concepts as one
repo-owned substrate family from the imported `adeu_semantic_forms` intake pack,
without laundering the imported bundle into precedent and without collapsing fallible
`NL -> ADEU` recovery into deterministic `ADEU -> ADEU` lowering?

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
- `V47-A` through `V47-F` are closed on `main` and now constitute the completed ANM /
  `D@1` policy-source, IR, facts, results, ledger, coexistence, ownership-transition,
  and consumer ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`.
- `V48-A` through `V48-E` are closed on `main` and now constitute the completed bounded
  policy-to-taskpack and worker-enforcement bridge recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`.
- `V49-A` through `V49-D` are closed on `main` and now constitute the completed
  bounded semantic substrate contract, bounded recovery, bounded deterministic
  lowering, and bounded semantic-seed bridge slices recorded in this draft.
- `vNext+120` is the current implementation-arc baseline on `main`.
- imported GPT Pro prototype bundles have been normalized under:
  - `examples/external_prototypes/adeu-semantic-forms-v0-bundle`
  - `examples/external_prototypes/adeu-symbol-audit-v0-bundle`
  - `examples/external_prototypes/odeu-sandbox-app`
  - `examples/external_prototypes/adeu-paper-semantic-workbench-poc`
- the imported bundles are currently governed only as:
  - imported external `X2` bundles;
  - `non_precedent`;
  - intake-only today.
- support/planning notes already exist for maintainer-side normalization:
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`

## Gap

The repo no longer lacks:

- typed repo-description and descriptive-to-normative binding over released `V45`;
- typed normative source / IR / consumer doctrine over released `V47`;
- typed policy-to-taskpack binding, compilation, worker-envelope, conformance, and
  bounded delegation over released `V48`;
- support/planning notes that tell the truth about the imported external bundles and
  their recommended moduleization order.

The repo no longer lacks the branch-local internal `V49` ladder.

The bounded semantic substrate family now covers, on `main`:

- released substrate contracts;
- released bounded recovery;
- released deterministic lowering into one narrow seed family; and
- released bounded semantic-seed bridge behavior into the already released `V48`
  binding / compile stack.

So the remaining work after `vNext+120` is not another implicit `V49-E`.

Any later widening beyond the shipped bounded semantic substrate family should be
treated as:

- a new planning decision;
- a downstream consumer or adjacent family choice; or
- a separately scoped future seam selection,

rather than as an ambient continuation automatically authorized by this planning
surface.

## Relationship To `V45`, `V47`, `V48`, And The Imported Bundles

`V45`, `V47`, `V48`, the support/planning prototype docs, and this new candidate family
are connected but non-identical.

`V45` asks:

- what repo entities, files, symbols, dependencies, and descriptive surfaces currently
  exist, and how are they typed?

`V47` asks:

- how should ADEU encode authoritative obligations inside markdown, normalize them into
  bounded semantic source, and bind later consumers?

`V48` asks:

- how should released policy and released scope become typed worker-execution
  boundaries, then prove conformance and bounded delegation?

The external-prototype support docs ask:

- how should imported bundles be preserved as evidence and normalized into repo-owned
  planning rather than treated as precedent-bearing overlays?

This new family asks:

- how should ADEU own one canonical semantic language / syntax-of-concepts substrate
  before broader consumers are wired?
- how should the repo freeze semantic identity, equivalence, and ambiguity doctrine
  before accepting recovery and lowering?
- how should later module families such as symbol audit or paper semantics consume that
  substrate, or intentionally remain independent?

So this family may constrain:

- later `V48`-adjacent lowering into taskpack-binding seed artifacts;
- later semantic consumers in symbol audit or paper semantic contract work;
- how natural-language recovery is demoted to one bounded, later lane rather than being
  treated as the semantic authority itself.

But it may not mint:

- new `V45` descriptive semantics;
- new `V47` normative-source semantics;
- new worker-execution semantics beyond released `V48`;
- direct precedent from the imported intake pack;
- broad multi-domain language or open-ended free-text planning by default;
- product surfaces such as CLI, API, or web routes in the first move.

Planning relationship:

- `V43` remains a valid connected candidate family from `v26`;
- `V44` remains a valid connected candidate family from `v27`;
- `V45` remains a valid connected candidate family from `v28`, but its bounded ladder
  is already closed on `main`;
- `V46` remains a valid connected candidate family from `v29`;
- `V47` remains a valid connected candidate family from `v30`, but its bounded ladder
  is already closed on `main`;
- `V48` remains a valid connected candidate family from `v31`, but its bounded ladder
  is already closed on `main`;
- this draft introduces a seventh connected candidate family rather than widening
  `V48`;
- this family should be read as the first imported-prototype moduleization family,
  starting with the semantic substrate rather than with a consumer.

## Recommended Family

- Family name: `V49`
- Family theme: ADEU semantic forms / canonical semantic language substrate
- Released earlier shaping inputs:
  - released `V45-A` through `V45-F`
  - released `V47-A` through `V47-F`
  - released `V48-A` through `V48-E`
- Support/planning shaping inputs:
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
  - `examples/external_prototypes/adeu-semantic-forms-v0-bundle`
- Connected candidate families not reopened or superseded here:
  - `V43`
  - `V44`
  - `V45`
  - `V46`
  - `V47`
  - `V48`
- Recommended first reference set for this branch:
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- Current family state for this branch:
  - `V49-A` closed on `main`
  - `V49-B` closed on `main`
  - `V49-C` closed on `main`
  - `V49-D` closed on `main`
- Recommended next path for this branch:
  - no further internal `V49` path currently selected
- Recommended next concrete arc for this branch if selected:
  - no further internal `V49` concrete arc currently selected
- Default path selection for this branch:
  - no further internal `V49` path currently selected after the bounded
    `V49-A` through `V49-D` ladder closed on `main`

This family/path recommendation is branch-local to the `v32` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected `V43`,
`V44`, `V45`, `V46`, `V47`, and `V48` branches remain in parallel planning scope.

## Recommended Next Family (`V49`)

`V49` should release a bounded semantic substrate around:

- parse profile artifacts over released ADEU anchors;
- semantic normal form artifacts;
- parse result artifacts;
- transform contract artifacts;
- canonical semantic identity law;
- canonical hash subject;
- semantic equivalence posture;
- explicit ambiguity posture and unsupported posture;
- deterministic, later lowering from semantic normal form into one narrow downstream
  seed.

The family should treat the imported intake pack as:

- shaping evidence;
- support-only source material;
- not the authority surface that the repo is releasing.

The family should treat natural-language recovery as:

- one released, bounded lane;
- not the source of semantic authority.

The family should treat deterministic lowering as:

- one released, bounded lane on `main`;
- not something that may be reopened implicitly inside later bridge code.

The family should treat later modules such as symbol audit or paper semantics as:

- downstream consumers or adjacent families;
- not part of the first semantic substrate release.
- if they later consume semantic primitives, they should consume released `V49`
  primitives or explicitly declare independence rather than drifting silently.

At minimum, later `V49` work should make explicit:

- what the smallest starter ADEU statement / calculus unit is;
- what operator / relation posture that starter unit allows;
- what semantic kinds or lane tags that starter unit allows;
- what the canonical semantic identity law is;
- what fields participate in the canonical hash subject;
- what fields are identity-participating versus projection-only or support-only;
- what counts as semantic equivalence versus merely similar paraphrase;
- what ambiguity outcomes are admissible;
- what unsupported outcomes are admissible;
- how one semantic normal form lowers into one narrow `V48`-adjacent seed without
  reopening released `V48` contracts;
- how that released seed may later flow into one narrow released `V48` bridge helper
  without laundering bridge authority back into lowering.

## Suggested `V49` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V49-A` | core semantic contracts | candidate parse-profile, semantic-normal-form, parse-result, and transform-contract surfaces plus starter statement calculus, identity/equivalence law, ambiguity law, and unsupported law | closed_on_main |
| `V49-B` | bounded recovery engine | candidate `NL -> ADEU` recovery lane over one starter domain with explicit ambiguity posture | closed_on_main |
| `V49-C` | deterministic lowering lane | candidate `semantic_normal_form -> taskpack_binding_spec_seed` lowering for one downstream target | closed_on_main |
| `V49-D` | downstream `V48` bridge | one narrow bridge helper into released `V48-A` / `V48-B` flows | closed_on_main |

These output names are planning-level candidate names, not lock-level schema authority.

`V49-A` through `V49-D` should be read together as the staged realization of the first
repo-owned semantic substrate family.

That is:

- `V49-A` freezes the substrate contracts and semantic identity law first;
- `V49-B` then adds bounded fallible recovery into those contracts;
- `V49-C` is now the released deterministic lowering move from those released
  contracts and released recovery outputs on `main`;
- `V49-D` is now the released bounded bridge into the released `V48` stack.

So the `A -> B -> C -> D` staging is an intentional separation between:

- substrate contract;
- fallible recovery;
- deterministic lowering;
- downstream operational bridge.

## Completed Final Path (`V49-D`)

`V49-D` is now closed on `main` as the bounded downstream bridge helper.

`V49-D` introduced:

- one repo-owned downstream bridge helper surface inside
  `packages/adeu_semantic_forms`;
- one bounded bridge input/output posture rich enough to cover:
  - exactly one released `adeu_taskpack_binding_spec_seed@1`;
  - exactly one released `V48-A` binding-profile posture;
  - exactly one released `V48-B` compile posture;
  - exactly one starter domain only:
    - `repo_policy_work`;
  - exactly one released lowering lineage posture:
    - released `V49-C` seed lineage only;
- one small deterministic reference fixture set proving:
  - successful bridge handoff from one released seed;
  - fail-closed rejection on released `V48-A` mismatch;
  - released-`binding_profile_ref` admissibility into `V48-B` with separate compile
    inputs;
  - deterministic bridge replay;
- no worker-envelope, conformance, delegation, or CLI/API/web consumer surfaces.

`V49-D` is bridge-first and still bounded:

- it may emit only the narrow helper outputs needed to hand a released seed into the
  already released `V48-A` / `V48-B` stack;
- it may not reopen `V48` semantics, emit worker-boundary artifacts, runtime
  execution behavior, or product consumers.

## Why This Path

- It was the narrowest safe consumer of the released `V49-C` seed contract.
- It keeps bridge behavior subordinate to already released semantic identity,
  recovery, and lowering doctrine rather than laundering bridge semantics back into
  `V49-C`.
- It proved that the frozen starter-domain seed can enter the released `V48-A` /
  `V48-B` stack without reopening binding or compile contracts.
- It lets later consumers depend on one explicit bridge helper instead of local ad hoc
  handoff code.
- It aligns with the current cross-module dependency table in
  `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`.

## Completed Final-Slice Boundary (`V49-D`)

`V49-D` should stay bounded to:

- one repo-owned package only:
  - `packages/adeu_semantic_forms`
- downstream bridge ownership only:
  - one bounded helper alongside the released lowering surface
  - bounded additions to package tests / fixtures
- exactly one released `V49-C` seed contract family only;
- exactly one released `V48-A` binding-profile posture only;
- exactly one released `V48-B` compile posture only;
- exactly one starter domain only:
  - `repo_policy_work`;
- exactly one released lowering lineage posture only;
- explicit deterministic fail-closed bridge posture only;
- deterministic reference fixtures only;
- repo-native unit tests only.

It should not attempt:

- generalized semantic transforms beyond the released starter calculus;
- recovery heuristics or new natural-language parsing behavior;
- reopening released `V48-A` binding-profile semantics or released `V48-B` compiled
  boundary semantics;
- worker execution or harness runtime wiring;
- symbol audit integration;
- paper semantic contract integration;
- simulation integration;
- CLI, API, or web surfaces.

## Current Internal Family State

`V49` is now closed on `main` and no further internal `V49` path is currently
selected.

Any later work should be treated as:

- a downstream consumer of released `V49` primitives;
- an adjacent semantic family; or
- a new planning branch,

not as an ambient continuation automatically authorized inside `v32`.

## Candidate Package Ownership

Package ownership should be treated as selected, in planning, for this first family:

- `packages/adeu_semantic_forms` is the likely first owning package for the semantic
  substrate;
- released `packages/adeu_repo_description` outputs are consumed as anchor inputs, not
  reopened as first-owner surfaces;
- released `packages/adeu_semantic_source` outputs are shaping context only, not
  silently widened as the owner of this new family;
- released `packages/adeu_agent_harness` outputs are downstream consumers only, not
  first-owner surfaces here.

This should be read as bounded family ownership for the semantic substrate rather than
as a universal claim about every later semantic consumer.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`

Connected but non-authorizing context docs are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`

Imported shaping surfaces that `V49` should learn from rather than reopen as authority
are:

- `examples/external_prototypes/adeu-semantic-forms-v0-bundle/CLAIMED_SCOPE.md`
- `examples/external_prototypes/adeu-semantic-forms-v0-bundle/source_tree`

## Planning Boundary

- no direct import of the external intake bundle into live repo package paths is
  authorized by this planning draft;
- no reopening of released `V45`, `V47`, or `V48` contracts is authorized by this
  planning draft;
- no widening of released `V49-B` natural-language recovery behavior beyond its
  bounded one-profile / one-domain posture is authorized by this planning draft;
- no reopening of released `V49-C` deterministic lowering semantics is authorized by
  this planning draft;
- no CLI, API, or web consumer surface is selected by this planning draft;
- no automatic supersession of the remaining imported bundles is authorized by this
  planning draft;
- no symbol-audit, paper-semantic, or simulation family is selected by this planning
  draft;
- no precedent-bearing authority is granted to the imported intake pack by this
  planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md",
  "baseline_arc": "vNext+120",
  "closed_prior_families": [
    "V45",
    "V47",
    "V48"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47",
    "V48",
    "V49"
  ],
  "branch_candidate_family": "V49",
  "branch_candidate_status": "selected_for_v32_planning_surface_not_repo_wide_family_selection",
  "connected_families_not_reopened_here": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47",
    "V48"
  ],
  "closed_current_family_paths": [
    "V49-A",
    "V49-B",
    "V49-D"
  ],
  "planned_current_family_paths": [],
  "default_next_arc_candidate_for_this_branch": null,
  "default_next_concrete_arc_candidate_for_this_branch": null,
  "family_architecture_doc": "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
  "pre_lock_companion_docs_expected": [
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v31.md"
  ],
  "planned_family_packages": [
    "packages/adeu_semantic_forms"
  ],
  "first_slice_active_packages": [
    "packages/adeu_semantic_forms"
  ],
  "package_selection_status": "selected_and_released_on_main",
  "family_theme": "adeu_semantic_forms_canonical_semantic_language_substrate",
  "branch_local_planning_selection_only": true,
  "imported_shaping_bundle": "examples/external_prototypes/adeu-semantic-forms-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_semantic_forms_contract_slice_consumed": "V49-A",
  "released_semantic_forms_recovery_slice_consumed": "V49-B",
  "released_semantic_forms_lowering_slice_consumed": "V49-C",
  "canonical_semantic_identity_required": true,
  "canonical_hash_subject_required": true,
  "semantic_equivalence_posture_required": true,
  "ambiguity_posture_required": true,
  "nl_to_adeu_recovery_released_on_main": true,
  "adeu_to_adeu_lowering_released_on_main": true,
  "v48_bridge_released_on_main": true,
  "consumer_surfaces_initially_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```
