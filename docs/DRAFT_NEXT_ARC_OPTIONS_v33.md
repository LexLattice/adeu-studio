# Draft Next Arc Options v33

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`, updated after the
bounded `V49` family closed on `main`, the repo-owned `adeu_semantic_forms` substrate
landed as a released package, and the next imported-prototype internalization move was
selected as the bounded `adeu_symbol_audit` B track rather than another implicit
continuation inside `V49`.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, the structural-reasoning assessment planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`, the repo self-description planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`, the applied benchmarking planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`, the authoritative normative markdown
planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`, the policy-to-taskpack and
worker-enforcement bridge planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md`, or
the semantic substrate planning branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`.

It also does not replace the support/planning posture of:

- `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`

Instead, it records an eighth connected candidate family and the next real
implementation-family move grounded in those support notes:

how should ADEU internalize one repo-owned, read-only symbol census / coverage /
semantic-audit family from the imported `adeu_symbol_audit` intake pack without
silently forking the released `repo_symbol_catalog@1` universe, without laundering the
imported bundle into precedent, and without deciding the later semantic-audit
vocabulary before the first bounded census/coverage slice is accepted?

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
  semantic substrate contract, bounded recovery, bounded deterministic lowering, and
  bounded semantic-seed bridge slices recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`.
- `V50-A` is closed on `main` and now constitutes the released bounded symbol census /
  coverage lane for the three-file `adeu_architecture_ir` pilot scope inside
  `packages/adeu_symbol_audit`.
- `vNext+121` is the current implementation-arc baseline on `main`.
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
- released semantic substrate surfaces already exist on `main` inside
  `packages/adeu_semantic_forms`, including:
  - canonical semantic contracts;
  - bounded `NL -> ADEU` recovery;
  - deterministic `ADEU -> ADEU` lowering into one narrow seed family;
  - bounded bridge behavior into the released `V48-A` / `V48-B` stack.

## Gap

The repo no longer lacks:

- typed repo-description and descriptive-to-normative binding over released `V45`;
- typed normative source / IR / consumer doctrine over released `V47`;
- typed policy-to-taskpack binding, compilation, worker-envelope, conformance, and
  bounded delegation over released `V48`;
- one released repo-owned semantic substrate package over bounded `V49`;
- support/planning notes that tell the truth about the imported external bundles and
  their recommended moduleization order.

The repo no longer lacks the branch-local internal `V49` ladder.

The missing layer after `vNext+121` is therefore not another implicit `V49-E`.

Today the repo still lacks a released way to:

- emit one repo-owned, one-audit-per-symbol semantic audit ledger over one released
  `V50-A` census while keeping closure truth separate from semantic uncertainty;
- freeze one audit-entry schema, one evidence-minimum law, and one bounded
  `audit_status` vocabulary inside the dedicated package rather than leaving them in a
  support-only prototype;
- decide explicitly whether the semantic/evidence vocabulary in the `B2` lane reuses
  released `V49` primitives or remains intentionally independent;
- keep CLI/orchestration and repo-wide scope widening deferred while the semantic
  audit-ledger contract is still being established.

The missing layer is therefore not:

- more `V45` descriptive extraction work;
- more `V49` semantic substrate work; or
- a runtime / product consumer surface.

The missing layer is a bounded symbol census / coverage / semantic-audit family.

## Relationship To `V45`, `V49`, And The Imported Bundles

`V45`, `V49`, the external-prototype support docs, and this new candidate family are
connected but non-identical.

`V45` asks:

- what repo entities, schemas, symbols, dependencies, and descriptive surfaces exist,
  and how are they typed?

`V49` asks:

- how should ADEU own one canonical semantic language / syntax-of-concepts substrate
  before broader consumers are wired?

The external-prototype support docs ask:

- how should imported bundles be preserved as evidence and normalized into repo-owned
  planning rather than treated as precedent-bearing overlays?

This new family asks:

- how should ADEU own one read-only symbol census / coverage family that is closure-
  oriented rather than only descriptive?
- how should one-audit-per-symbol semantic audit work remain explicitly later than the
  first census/coverage slice?
- how should the family stay explicit about its relationship to released
  `repo_symbol_catalog@1` rather than silently forking the repo’s symbol universe?
- how should the later semantic-audit lane either consume released `V49` primitives or
  explicitly declare independence rather than drifting into a second hidden semantic
  substrate?

`V50-A` should therefore be read as:

- read-only and census-first;
- explicit about overlap with `repo_symbol_catalog@1`;
- explicit that overlap is non-trivial rather than parity-based:
  - reuse released `repo_symbol_catalog@1` as overlap/anchor context;
  - do not claim symbol-kind parity with released `repo_symbol_catalog@1`;
  - introduce `local_function` only as one explicit family-local extension in the
    census/closure lane;
  - permit compatibility with the released textual symbol-id shape where declared,
    without claiming parity with the released `SymbolKind` enum;
  - keep that extension explicit, non-superseding, and identity-law-compatible where
    declared;
- independent from the `V49` primitive-reuse decision for now.

`V50-B` should therefore be read as:

- later than `V50-A`;
- the point where the semantic vocabulary reuse-vs-independence decision must be made
  explicitly before release.

So this family may constrain:

- later symbol audit ledger work over one frozen census;
- how later Module B work may consume released `V49` primitives or explicitly declare
  independence;
- how later CLI/orchestration consumers are kept subordinate to released census,
  coverage, and audit contracts.

But it may not mint:

- new `V45` descriptive semantics;
- new `V49` semantic substrate semantics by default;
- direct precedent from the imported intake pack;
- repo-wide symbol audit entitlement by default;
- runtime mutation or worker-execution surfaces;
- CLI, API, or web product surfaces in the first move.

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
- `V49` remains a valid connected candidate family from `v32`, but its bounded ladder
  is already closed on `main`;
- this draft introduces an eighth connected candidate family rather than widening
  `V49`;
- this family should be read as the second imported-prototype moduleization family,
  starting with read-only census/coverage rather than with semantic audit or CLI
  surfaces.

## Recommended Family

- Family name: `V50`
- Family theme: ADEU symbol census, coverage, and semantic audit family
- Released earlier shaping inputs:
  - released `V45-A` through `V45-F`
  - released `V49-A` through `V49-D`
- Support/planning shaping inputs:
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
  - `examples/external_prototypes/adeu-symbol-audit-v0-bundle`
- Connected candidate families not reopened or superseded here:
  - `V43`
  - `V44`
  - `V45`
  - `V46`
  - `V47`
  - `V48`
  - `V49`
- Recommended first reference set for this branch:
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
  - `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
  - `examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md`
- Current family state for this branch:
  - `V50-A` is closed on `main`
- Recommended next path for this branch:
  - `V50-B`
- Recommended next concrete arc for this branch if selected:
  - `vNext+122`
- Default path selection for this branch:
  - select `V50-B` as the next default candidate
  - treat that default as the semantic-audit ledger lane prior to any CLI widening

This family/path recommendation is branch-local to the `v33` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected `V43`,
`V44`, `V45`, `V46`, `V47`, `V48`, and `V49` branches remain in parallel planning
scope.

## Closed Earlier Families And Surfaces

`V45` should now be read as the released descriptive symbol substrate:

- one canonical `repo_symbol_catalog@1` and related descriptive surfaces;
- broad repo-owned symbol inventory and dependency context;
- released symbol-kind vocabulary:
  - `module`
  - `class`
  - `function`
  - `method`
  - `attribute`
- not one-audit-per-symbol closure law.

`V49` should now be read as the released semantic substrate:

- canonical semantic contracts;
- bounded natural-language recovery;
- deterministic lowering into one narrow seed family;
- bounded bridge behavior into the released `V48` stack.

The imported `adeu_symbol_audit` intake bundle should now be read as:

- shaping evidence and support-only source material;
- a bounded pilot-scope concept bundle over `packages/adeu_architecture_ir`;
- not a released repo-owned module.

None of those surfaces, by themselves, yet solve:

- one repo-owned one-audit-per-symbol semantic audit ledger over one released census;
- one bounded audit-entry schema, evidence-minimum law, and semantic-uncertainty
  vocabulary for that ledger lane;
- one explicit family decision about whether `V50-B` reuses released `V49`
  primitives or remains intentionally independent.

`V50` is the planning move that fills that family gap without reopening released
descriptive or semantic-substrate baselines.

## Recommended Next Family (`V50`)

`V50` should release a bounded read-only symbol audit family around:

- pilot scope manifest artifacts;
- deterministic symbol census artifacts;
- mechanical coverage / closure report artifacts;
- later one-audit-per-symbol semantic audit ledger artifacts;
- later bounded CLI/orchestration surfaces.

The family should treat the imported intake pack as:

- shaping evidence;
- support-only source material;
- not the authority surface the repo is releasing.

The family should treat released `repo_symbol_catalog@1` as:

- upstream descriptive context and overlap anchor;
- not something `V50` is allowed to silently fork or supersede.

The family should treat divergence from released `repo_symbol_catalog@1` as lawful only
when the delta is explicit and bounded, including:

- narrower pilot scope;
- stricter coverage / closure ordering;
- one explicit family-local `local_function` kind in the read-only census lane.

The family should treat divergence from released `repo_symbol_catalog@1` as unlawful
when it would:

- silently change shared symbol identity law;
- silently change the meaning of shared symbol kinds;
- claim parity or supersession where the family is actually narrower or extended; or
- present the family-local `local_function` extension as if it were already part of the
  released descriptive baseline.

The family should treat released `V49` semantic primitives as:

- adjacent released substrate;
- not automatically consumed by `V50-A`;
- something `V50-B` must either consume explicitly or explicitly decline before
  release.
- `V50-A` artifacts should remain semantically minimal enough that either later choice
  remains open.

At minimum, later `V50` work should make explicit:

- what symbol kinds are included in the bounded family;
- what the symbol identity law is for the census family;
- whether shared symbol kinds reuse the released textual `symbol:{module_path}:{qualname}:{symbol_kind}`
  identity law from `repo_symbol_catalog@1`, and if not, what exact delta is selected;
- what one pilot-scope manifest contains and how scope closure is checked;
- what the coverage closure law is over one frozen census;
- what counts as missing, unexpected, or duplicate audit coverage;
- how the later semantic-audit ledger relates to the frozen census;
- whether `V50-B` reuses released `V49` primitives or intentionally remains
  independent;
- how later CLI/orchestration consumers remain subordinate to released `V50`
  artifacts.

## Suggested `V50` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V50-A` | symbol census + coverage lane | candidate `adeu_symbol_audit_scope_manifest@1`, candidate `adeu_symbol_census@1`, and candidate `adeu_symbol_audit_coverage_report@1` over one bounded pilot scope | closed_on_main |
| `V50-B` | semantic audit ledger lane | candidate `adeu_symbol_semantic_audit@1` with one-audit-per-symbol posture over one released census | planned_selected_next |
| `V50-C` | CLI / orchestration seam | candidate `adeu_symbol_audit_session@1` and bounded runner / CLI doctrine | planned_later_not_selected_here |

These output names are planning-level candidate names, not lock-level schema
authority.

`V50-A` through `V50-C` should be read together as the staged realization of the first
repo-owned symbol audit family.

That is:

- `V50-A` intentionally freezes read-only census / coverage law first;
- `V50-B` then adds one semantic-audit ledger over that frozen census;
- `V50-C` is later and only selected after the read-only contracts are already
  accepted.

So the `A -> B -> C` staging is an intentional separation between:

- read-only census and closure;
- later semantic-audit claims;
- still-later user-facing orchestration.

## Recommended Next Path (`V50-B`)

Implement the bounded semantic audit-ledger lane next.

`V50-B` should introduce:

- one repo-owned semantic-audit helper surface inside:
  - `packages/adeu_symbol_audit`
- one canonical semantic-audit artifact candidate rich enough to cover:
  - exactly one released `adeu_symbol_census@1` only;
  - exactly one audit entry per released census symbol only;
  - exactly one starter `audit_status` vocabulary only;
  - exactly one bounded evidence-minimum law only;
- one explicit separation between:
  - closure truth already frozen by released `V50-A`; and
  - semantic uncertainty carried by the new audit ledger;
- one explicit family decision about whether semantic/evidence vocabulary:
  - reuses released `V49` primitives; or
  - remains intentionally independent;
- one small deterministic fixture set rich enough to cover:
  - accepted one-audit-per-symbol replay over one released census;
  - low-confidence handling;
  - unresolved handling;
  - fail-closed rejection on missing evidence or duplicate audit entries.

`V50-B` is ledger-first and still bounded:

- it may emit semantic-audit ledger artifacts plus bounded diagnostics;
- it may not yet emit CLI surfaces, repo-wide audit entitlement, or runtime mutation
  behavior.

## Why This Path

- It is the narrowest safe next consumer of the imported `adeu_symbol_audit` concept
  bundle after the released `V50-A` census/coverage baseline.
- It lets the repo freeze semantic-audit entry law without reopening the already
  closed read-only scope, identity, and closure contracts.
- It keeps the separation between completion accounting and semantic uncertainty
  explicit rather than letting audit claims silently redefine closure truth.
- It forces the `V49` primitive reuse-vs-independence decision to become explicit
  before the repo accepts a second semantic/evidence idiom.
- It keeps CLI/orchestration later, after the ledger contract is already inspectable.

## First-Slice Boundary (`V50-B`)

`V50-B` should stay bounded to:

- one repo-owned package only:
  - `packages/adeu_symbol_audit`
- one released census input only:
  - one released `adeu_symbol_census@1`
- one released coverage baseline only:
  - released `V50-A` closure truth remains fixed input context and is not reopened
- one audit-entry cardinality law only:
  - exactly one semantic-audit entry per census symbol
- one starter `audit_status` vocabulary only
- one starter `confidence_band` vocabulary only
- one evidence-minimum law only:
  - every audit entry must carry at least one `evidence_ref`
- one explicit semantic-vocabulary posture only:
  - either consume released `V49` primitives explicitly; or
  - explicitly remain independent
- deterministic local fixtures only;
- repo-native unit tests only.

It should not attempt:

- reopening released `V50-A` scope, census, or coverage law;
- CLI, API, or web surfaces;
- repo-wide scope;
- write-capable or runtime mutation surfaces;
- a second hidden semantic substrate outside the explicit reuse-vs-independence
  decision;
- direct import of the external intake bundle into live package paths.

## Follow-On Paths Inside `V50`

### `V50-B`

Semantic audit ledger lane:

- add one-audit-per-symbol semantic audit entries over one released census;
- freeze audit entry schema, evidence minimums, and allowed `audit_status` values;
- decide explicitly whether semantic/evidence vocabulary:
  - reuses released `V49` primitives; or
  - is intentionally independent.

### `V50-C`

CLI / orchestration seam:

- later family work may widen from released census / coverage / audit artifacts into
  one bounded CLI or runner surface;
- that seam is explicitly later and not selected in the first family move.

## Candidate Package Ownership

Package ownership should remain planning-bound for now.

The first planning pass should therefore assume:

- `packages/adeu_symbol_audit` is the likely first owning package for this family;
- released `packages/adeu_repo_description` outputs are consumed as overlap/anchor
  inputs, not reopened as first-owner surfaces;
- released `packages/adeu_semantic_forms` outputs are adjacent substrate only and are
  not silently made mandatory in `V50-A`;
- the later `V50-B` lane must make the semantic primitive reuse-vs-independence
  decision explicit before release.

This should be read as intentional family restraint, not as missing planning detail.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md`
- `docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `examples/external_prototypes/adeu-symbol-audit-v0-bundle/ALIGNMENT.md`

Connected but non-authorizing context docs are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`

Imported shaping surfaces that `V50` should learn from rather than reopen as authority
are:

- `examples/external_prototypes/adeu-symbol-audit-v0-bundle/CLAIMED_SCOPE.md`
- `examples/external_prototypes/adeu-symbol-audit-v0-bundle/source_tree`

Concrete released substrate anchors for this family direction are:

- `apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json`
  as one released `repo_symbol_catalog@1` anchor artifact;
- `packages/adeu_repo_description/schema/repo_symbol_catalog.v1.json`
  as the authoritative schema anchor for that released descriptive surface;
- released `packages/adeu_semantic_forms` contracts on `main` as adjacent semantic
  substrate context, not as mandatory `V50-B` dependencies;
- released `packages/adeu_symbol_audit` census / coverage surfaces on `main` as the
  fixed upstream baseline for the `V50-B` ledger lane.

## Planning Boundary

- no direct import of the external intake bundle into live repo package paths is
  authorized by this planning draft;
- no reopening of released `V45` or released `V49` contracts is authorized by this
  planning draft;
- no silent fork of `repo_symbol_catalog@1` identity or scope is authorized by this
  planning draft;
- no CLI, API, or web consumer surface is selected by this planning draft;
- no repo-wide scope widening is selected by this planning draft;
- no semantic or evidence vocabulary supersession of released `V50-A` closure truth is
  authorized by this planning draft;
- no precedent-bearing authority is granted to the imported intake pack by this
  planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md",
  "baseline_arc": "vNext+121",
  "closed_prior_families": [
    "V45",
    "V47",
    "V48",
    "V49"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47",
    "V48",
    "V49",
    "V50"
  ],
  "branch_candidate_family": "V50",
  "branch_candidate_status": "selected_for_v33_planning_surface_not_repo_wide_family_selection",
  "connected_families_not_reopened_here": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47",
    "V48",
    "V49"
  ],
  "closed_current_family_paths": [
    "V50-A"
  ],
  "planned_current_family_paths": [
    "V50-A",
    "V50-B",
    "V50-C"
  ],
  "default_next_arc_candidate_for_this_branch": "V50-B",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+122",
  "family_architecture_doc": "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
  "pre_lock_companion_docs_expected": [
    "docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md",
    "docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v32.md"
  ],
  "planned_family_packages": [
    "packages/adeu_symbol_audit"
  ],
  "first_slice_active_packages": [
    "packages/adeu_symbol_audit"
  ],
  "package_selection_status": "selected_in_planning_not_locked_yet",
  "family_theme": "adeu_symbol_census_coverage_and_semantic_audit_family",
  "branch_local_planning_selection_only": true,
  "imported_shaping_bundle": "examples/external_prototypes/adeu-symbol-audit-v0-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "released_repo_symbol_catalog_family_consumed": "V45",
  "released_semantic_forms_family_adjacent": "V49",
  "released_v50a_census_coverage_required": true,
  "single_pilot_scope_initially_required": true,
  "pilot_scope_default": "packages/adeu_architecture_ir",
  "pilot_scope_reference_files": [
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py"
  ],
  "symbol_kinds_initially_required": [
    "class",
    "function",
    "method",
    "local_function"
  ],
  "repo_symbol_catalog_symbol_kind_parity_not_claimed": true,
  "local_function_family_local_extension_required": true,
  "lawful_divergence_from_repo_symbol_catalog_frozen": [
    "narrower_pilot_scope",
    "stricter_coverage_closure_ordering",
    "explicit_local_function_extension"
  ],
  "unlawful_divergence_from_repo_symbol_catalog_forbidden": [
    "silent_identity_law_change",
    "silent_shared_symbol_kind_meaning_change",
    "parity_or_supersession_claim",
    "implicit_local_function_descriptive_baseline_claim"
  ],
  "symbol_catalog_overlap_rule_required": true,
  "symbol_identity_law_compatibility_declaration_required": true,
  "deterministic_replay_over_exact_pilot_scope_bytes_required": true,
  "coverage_closure_law_required": true,
  "semantic_vocab_dependency_decision_selected_in_v50b": true,
  "v50a_artifacts_semantically_minimal_to_keep_v50b_choice_open": true,
  "semantic_ledger_selected_next": true,
  "cli_and_orchestration_initially_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```
