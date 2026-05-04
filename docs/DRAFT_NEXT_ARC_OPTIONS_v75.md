# Draft Next Arc Options v75

Status: planning handoff after `vNext+238` / `V84-C` merged on `main`, after
the `V84` family closeout pass, after the combined `V68` through `V84`
dogfood probe, and after the post-`V84` continuation roadmap.

Authority layer: planning.

This draft records the post-`V84` frontier. It does not authorize semantic
declaration runtime, obligation expansion, worker execution, implementation,
code edits, command execution, tool invocation, target mutation, PR creation,
commit, merge, release, product authorization, graph-memory authority,
recursive policy amendment, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v74.md`, which selected the `V84` work-packet
activation-review family. `vNext+236`, `vNext+237`, and `vNext+238` then
closed `V84-A`, `V84-B`, and `V84-C` without creating additional family
selector versions.

## Current Frontier

- `V68` is closed on `main` as the ARC series cartography family.
- `V69` is closed on `main` as the recursive candidate-intake family.
- `V70` is closed on `main` as the candidate review-classification family.
- `V71` is closed on `main` as the candidate ratification-review family.
- `V72` is closed on `main` as the contained integration-review family.
- `V73` is closed on `main` as the candidate outcome-review family.
- `V74` is closed on `main` as the operator-projection family.
- `V75` is closed on `main` as the dispatch-review family.
- `V76` is closed on `main` as the reconciliation / arbiter review family.
- `V77` is closed on `main` as the runtime-permission review family.
- `V78` is closed on `main` as the runtime execution authority review family.
- `V79` is closed on `main` as the controlled execution review family.
- `V80` is closed on `main` as the external branch activation review family.
- `V81` is closed on `main` as the cross-corpus governance family.
- `V82` is closed on `main` as the corpus-ingestion authority-review family.
- `V83` is closed on `main` as the semantic implementation-specification
  review family.
- `V84` is closed on `main` as the work-packet activation-review family.
- latest closed implementation arc: `vNext+238`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v74.md`
- next planning obligation: select and review `V85` as the next family outside
  closed `V84`.

The combined `V68` through `V84` support dogfood test is recorded in:

- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_COMBINED_DOGFOOD_TEST_v0.json`

That support result says the closed families compose as intended and that
`V84` closed work-packet activation review without work-packet activation,
implementation-lock creation, code edits, command execution, tool invocation,
target mutation, PR creation, commit, merge, release, product authorization,
graph-memory authority, recursive policy amendment, or `V85` selection.

## Next Planning Question

`V84` made a later implementation-lock package reviewable:

```text
V83 projection packet
  -> V84 activation-review request
  -> scope / target / validation / exception review
  -> readiness summary
  -> later canonical implementation-lock pressure
```

The next missing layer is not implementation and not the lock itself. The
post-`V84` support roadmap identifies a more upstream institutional seam:

```text
natural task / code context
  -> typed semantic declaration
  -> canonical pointer lookup
  -> class-indexed obligation expansion
  -> evidence contract and edge probes
  -> independent audit
  -> deterministic closeout routing
```

The immediate family should type the first part of that circuit. Should the
next family be `V85`: semantic declaration and canonical meta-list review?

This selector intentionally treats `V85` as semantic declaration **review**,
not semantic declaration authority, obligation expansion, implementation
authority, worker execution, runtime transition, product authorization, graph
authority, or recursive policy authority.

Controlling invariant:

```text
V85 may make semantic declaration and canonical pointer lookup reviewable,
but it may not expand those declarations into implementation authority,
worker execution, runtime transition, product authorization, release,
graph-memory authority, recursive policy amendment, or later-family selection.
```

## Recommended Next Pressure

- family: `V85`
- proposed family name:
  - `V85: semantic declaration and canonical meta-list review`
- recommended planning posture:
  - select `V85` as the next standalone bridge family after `V84`;
  - select `V85-A` as the next default candidate for `vNext+239`;
  - consume `V68` through `V84` family closeouts and the combined dogfood as
    the repo-native governance substrate;
  - consume the post-`V84` roadmap and canonical semantic declaration
    meta-loop support note as planning/support sources;
  - consume released `V84-C` readiness, handoff, and family closeout fixtures
    as concrete source rows;
  - define declaration-review requests, declaration source indexes, and
    non-authority guardrails before canonical lookup indexes, obligation
    registries, summaries, or post-declaration handoffs are represented;
  - keep resident-model declarations candidate-only unless source-bound by
    concrete operator / repo / support rows and routed through explicit
    ambiguity or registry-gap postures.

`V85` should type the question: "what semantic act is this turn asking the
system to review?" It must not claim that the model understands the whole
institution or that the declaration by itself authorizes obligations,
implementation, audit, closeout routing, or runtime behavior.

The family should integrate these conceptual edge patches before the
`vNext+239` starter:

- stable `semantic_declaration_session_ref` across declaration, lookup,
  registry, summary, and handoff rows;
- explicit transition from declared act candidate to lookup result to selected
  declaration, with `V85-A` limited to candidates;
- row-shaped semantic act witnesses, negative cues, and resident-model
  competency requirements;
- fail-closed ambiguity, abstain, malformed input, unknown pointer, and
  registry-gap semantics;
- pointer competency and claim horizon fields so opaque pointer success cannot
  prove natural binding correctness;
- operator/class registry domain separation and obligation-family relation
  kinds;
- handoff sequencing that keeps evidence, audit, and closeout routing
  downstream of obligation expansion review.

## Proposed Family Decomposition

`V85` should be reviewed as a three-slice family:

| Slice | Role |
|---|---|
| `V85-A` | turn semantic declaration request, semantic declaration source index, and non-authority guardrail |
| `V85-B` | canonical meta lookup index, semantic operator/class registry, obligation-family registry, and pointer lookup fixtures |
| `V85-C` | semantic declaration review summary, post-semantic-declaration-review handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`V85-A` should be the first active slice. Candidate starter surfaces:

- `repo_turn_semantic_declaration_request@1`
- `repo_semantic_declaration_source_index@1`
- `repo_semantic_declaration_non_authority_guardrail@1`

Recommendation: select `V85-A` as the next default candidate after this
selector, with `vNext+239` as the canonical starter bundle if no intervening
arc claims that number.

Later `V85` surfaces should remain planning-layer until their own starter
locks:

- `repo_canonical_meta_lookup_index@1`
- `repo_semantic_operator_class_registry@1`
- `repo_obligation_family_registry@1`
- `repo_semantic_pointer_lookup_fixture@1`
- `repo_semantic_declaration_review_summary@1`
- `repo_post_semantic_declaration_review_handoff@1`
- `repo_semantic_declaration_family_closeout_alignment@1`

Post-`V85-A` continuation posture: after `vNext+239` closes on `main`, select
`V85-B` as the next default candidate for the next canonical starter bundle.
Machine-detectable restatement: select `V85-B` as the next default candidate.
That selection remains inside the already selected `V85` family and does not
create a new next-arc-options selector version.

Post-`V85-B` continuation posture: after the `V85-B` slice closes on `main`,
select `V85-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `V85` family and
does not create a new next-arc-options selector version.

## Non-Selection

This selector handoff does not select:

- obligation expansion, evidence contracts, edge probe plans, reviewer
  taskpacks, audit reports, deterministic closeout transition tables, or
  remand routing;
- implementation, code edits, command execution, tool invocation, target
  mutation, work-packet execution, or implementation-lock creation;
- worker assignment, dispatch execution, controlled execution, runtime
  permission, or meta-orchestrator runtime transition;
- Morphic UX runtime changes, UI renderer rewrites, or composer geometry
  runtime fixes;
- direct OAI / Codex harness runtime behavior, provider mutation, model
  selection, quota controls, or tool broker authority;
- PR creation, commit, merge, release, or released-truth authority;
- product launch, product-market validation, or product authorization;
- corpus ingestion, customer-data handling, connector activation, endpoint
  access, or data transfer;
- external branch activation, `V43` contest participation, external
  submission, or benchmark truth;
- graph-memory authority or living-memory runtime;
- recursive policy amendment;
- `V86` or any later family.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`V85` is planning-ready because the repo now has:

- released `V83` semantic implementation-specification review substrate;
- released `V84` activation-review substrate;
- a post-`V84` roadmap that maps the semantic declaration meta-loop;
- a support architecture note describing the resident-model competency
  contract and canonical pointer loop.

`V85-A` request recordability must be weaker than eligibility. A semantic
declaration request may be recorded when it cites an operator turn, repo
context, support doctrine, released `V84-C` substrate, or explicit absence
rows. An eligible semantic declaration-review request must cite:

- released `V84-C` readiness / handoff / closeout substrate or explicit
  source posture;
- concrete operator / repo / task context source rows;
- direct/current source witness rows for the proposed semantic act;
- a stable `semantic_declaration_session_ref`;
- candidate-only declaration status, with canonical lookup and selected
  declaration status not claimed by `V85-A`;
- non-goal or boundary rows showing that implementation and obligation
  expansion are not being claimed;
- non-authority guardrails.

Support docs, model output, generated declarations, operator preference, or a
natural-language task label may contextualize a request, but they cannot be
the only eligibility sources. Ambiguous, unknown, malformed, or non-canonical
bindings must be represented as ambiguity, abstain, registry-gap, blocked, or
future-family-only rows rather than smoothed into selected declarations.

`V85` must not be used if the only evidence is:

- a model suggestion that a task "looks like" a class;
- an opaque pointer with no lookup row or explicit abstain posture;
- opaque pointer success being used as proof of natural binding correctness;
- a support note without concrete source refs for the current turn;
- a generated declaration with no source witnesses;
- an unknown class repaired into the nearest registry class;
- an operator request to implement rather than to declare and review the
  semantic act;
- a canonical class label treated as implementation or runtime authority.

## Recommended Review Bundle

Review the first `V85` planning bundle as:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v75.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85C_IMPLEMENTATION_MAPPING_v0.md`

The future active starter trio should be:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS239.md`
- `docs/ASSESSMENT_vNEXT_PLUS239_EDGES.md`

That future starter should select only `V85-A`.

## Likely Post-`V85` Pressure

Do not select it here, but the likely immediate continuation after `V85` is:

```text
V86: obligation expansion / evidence contract / edge probe plan review
```

Possible longer semantic meta-loop continuation:

```text
V85 semantic declaration / canonical pointer lookup
  -> V86 obligation expansion / evidence contract / edge probe plan
  -> V87 reviewer / auditor taskpack and audit artifact review
  -> V88 deterministic closeout transition table / remand routing
```

Those labels are planning handles only. A future selector should choose the
actual next family based on released `V85-C` rows.
