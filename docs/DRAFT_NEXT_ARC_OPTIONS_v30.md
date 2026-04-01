# Draft Next Arc Options v30

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`, updated after the
authoritative normative markdown / `D@1` seed bundle was consolidated into a bounded
separate-but-connected infra family direction.

This draft does not automatically supersede the contest-participation planning branch in
`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`, the structural-reasoning assessment planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`, the repo self-description planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`, or the applied benchmarking planning
branch in `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`.

Instead, it records a fifth connected candidate family:

how should ADEU Studio write authoritative obligations inside markdown, compile them
into bounded normalized semantics, evaluate them against fact-only observations, and
track live obligation state without inferring policy from prose, reopening the completed
`V45` branch, or laundering authority out of checker or ledger artifacts?

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

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` through `V41-F` are closed on `main`.
- `V42-A` through `V42-G4` are closed on `main`.
- `V45-A` through `V45-F` are closed on `main` and now constitute the completed bounded
  repo self-description ladder recorded in `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`.
- `V47-A` and `V47-B` are closed on `main` and now constitute the released ANM / `D@1`
  substrate plus the first schema/example/vocabulary hardening slice for this family.
- `vNext+107` is the current baseline implementation state on `main`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md` records one connected candidate family:
  - `V43`
  - ADEU external governed contest participation substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` records one connected candidate family:
  - `V44`
  - ADEU structural reasoning assessment substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md` records one connected candidate family:
  - `V45`
  - ADEU repo self-description substrate
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` records one connected candidate family:
  - `V46`
  - ADEU applied benchmarking substrate
- the ANM / `D@1` seed bundle now records a fifth connected planning seed:
  - markdown-native authoritative normative substrate
  - bounded `D@1` dialect
  - normalized `D-IR`
  - bootstrap predicate contracts
  - checker fact bundles
  - policy evaluation result sets
  - policy obligation ledger

## Gap

The repo still lacks a released way to:

- express machine-checkable obligations inside markdown without inferring obligation from
  arbitrary prose;
- separate:
  - authoritative normative source;
  - normalized semantic IR;
  - observed checker facts;
  - run-specific evaluation results;
  - cross-run obligation state;
- make selector, predicate, evidence, and failure posture explicit rather than hidden in
  evaluator or checker code;
- preserve a bounded operational obligation ledger without letting the ledger mint
  policy, waiver, or deferral authority by itself;
- adopt authoritative normative markdown in standalone or companion posture without
  forcing repo-wide migration of current lock/planning markdown;
- provide later consumers with a policy-bearing substrate that is narrower and less
  prose-ambiguous than current freeform markdown alone.

The missing layer is therefore not more descriptive self-modeling and not yet a
recursive execution or amendment engine.

The missing layer is an ADEU authoritative normative markdown substrate.

## Relationship To `V43`, `V44`, `V45`, And `V46`

`V43`, `V44`, `V45`, `V46`, and this new candidate family are connected but
non-identical.

`V43` asks:

- what kind of external contest world is this?
- what is lawful?
- what is measured?
- where could reasoning AI help?

`V44` asks:

- is a candidate model structurally suitable to inhabit an explicit inferential
  skeleton under ADEU discipline?

`V45` asks:

- what does the ADEU repo currently contain, and how are those surfaces typed and
  governed as a descriptive artifact system?

`V46` asks:

- how should ADEU define benchmark families, projections, execution contexts, run
  traces, validation posture, and benchmark diagnostics as reusable governed objects?

This new family asks:

- how should ADEU encode authoritative obligations inside markdown?
- how should those obligations compile into bounded normalized semantics?
- how should fact-only checker observations and evaluator results remain distinct from
  live ledger state?
- how should later consumers bind descriptive or benchmark artifacts into policy-bearing
  rules without laundering authority out of facts, results, or ledgers?

So this family may constrain:

- how later lock or policy-bearing docs express obligations;
- how `V45` descriptive artifacts are consumed normatively;
- how later benchmark or assessment branches express policy checks over bounded artifact
  worlds;
- how live obligation state is tracked across repeated runs and closeout.

But it may not mint:

- direct mutation entitlement;
- recursive execution authority;
- waiver or deferral authority by checker or ledger artifact alone;
- contest doctrine;
- benchmark doctrine;
- automatic supersession of current markdown authority docs.

Planning relationship:

- `V43` remains a valid connected candidate family from `v26`;
- `V44` remains a valid connected candidate family from `v27`;
- `V45` remains a valid connected candidate family from `v28`, but its bounded ladder is
  already closed on `main`;
- `V46` remains a valid connected candidate family from `v29`;
- this draft introduces a fifth connected candidate family rather than replacing any of
  them;
- this family should not be read as `V45-G`;
- `V45-F` already released a descriptive-to-normative binding seam over released
  descriptive objects, and this new family should instead be read as the lower-level
  policy-source / IR / fact / result / ledger substrate that later consumers may use.

## Recommended Family

- Family name: `V47`
- Family theme: ADEU authoritative normative markdown and bounded `D@1` compilation
  substrate
- Released earlier shaping inputs:
  - `V41-A` through `V41-F`
  - `V45-A` through `V45-F`
- Connected candidate families not reopened or superseded here:
  - `V43`
  - `V44`
  - `V45`
  - `V46`
- Recommended architecture reference:
  - `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- Recommended first reference set for this branch:
  - `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
  - `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
  - `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`
  - `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
  - `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
  - `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
- Recommended next path for this branch:
  - `V47-C`
- Recommended next concrete arc for this branch if selected:
  - `vNext+108`
- Default path selection for this branch:
  - select `V47-C` as the next default candidate
  - treat that default as the bounded next coexistence/adoption lane after released
    `V47-A` plus `V47-B`

This family/path recommendation is branch-local to the `v30` planning surface.

It is not, by itself, a repo-wide next-family resolution while the connected `V43`,
`V44`, `V45`, and `V46` branches remain in parallel planning scope.

## Closed Earlier Families And Surfaces

`V45` should now be read as a released descriptive substrate:

- entity and schema-family self-description;
- symbol and dependency self-description;
- arc dependency posture;
- test-intent visibility;
- optimization diagnostics;
- descriptive-to-normative binding doctrine over released descriptive objects.

`V45` did not release:

- authoritative normative source syntax inside markdown;
- normalized normative IR;
- checker fact bundles;
- evaluator result sets;
- live obligation ledgers.

`V46` should now be read as the currently planned applied benchmarking substrate.

`V46` may later consume or be constrained by this family, but it is not reopened or
superseded here.

`V47` is the planning move that generalizes the normative authoring and obligation-state
thread without reopening descriptive self-modeling, benchmarking doctrine, or current
markdown lock authority.

`V47-A` should now be read as a released first substrate on `main`:

- markdown-native ANM source posture;
- explicit authoritative `D@1` blocks;
- normalized `D-IR`;
- semantic bootstrap predicate contracts;
- fact-only checker bundles;
- run-specific evaluation result sets;
- cross-run obligation ledger projection.

`V47-A` did not release:

- widened fact-kind or provenance vocabularies beyond the bounded starter set;
- broader current-markdown migration or adoption doctrine;
- imported O-owned selector handles or E-owned predicate registries;
- downstream execution, mutation, waiver, deferral, or approval authority.

## Recommended Next Family (`V47`)

`V47` should release a bounded normative-compilation doctrine around:

- markdown-native ANM container posture;
- opt-in authoritative fenced `D@1` blocks;
- bounded typed clause language;
- normalized semantic `D-IR`;
- bootstrap predicate contracts with explicit evidence and failure posture;
- fact-only checker bundles;
- run-specific evaluation result sets;
- cross-run obligation ledger state;
- explicit no-prose-inference posture outside `D@1`;
- explicit coexistence and companion-doc posture relative to current markdown doctrine.

The family should treat authoritative policy as a pipeline:

```text
ANM source markdown
  -> D@1 source blocks
  -> normalized D-IR
  -> checker fact bundles
  -> policy evaluation result sets
  -> policy obligation ledger
```

The family should treat later recursive-governance or execution consumers as:

- downstream consumers of this substrate;
- not the first release inside this family.

The family should treat waiver and deferral issuance as:

- externally authorized inputs or later governed artifacts;
- not authorities minted by result sets or ledger state by default.

At minimum, later `V47` work should make explicit:

- exact `ONLY_IF` and `UNLESS` applicability semantics;
- zero-match selector policy;
- result-to-ledger mapping posture;
- clause-scope `unknown_resolution` posture without fake ledger-row creation;
- frozen starter checker-fact kind vocabulary;
- frozen starter provenance-mode vocabulary;
- concrete example ANM source plus compiled companion artifacts;
- the boundary between bootstrap string selectors / bootstrap predicate contracts and
  later O-owned selector handles or E-owned predicate registries.

## Suggested `V47` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V47-A` | bounded ANM / `D@1` compilation substrate | released `d1_normalized_ir@1`, `predicate_contracts_bootstrap@1`, `checker_fact_bundle@1`, `policy_evaluation_result_set@1`, and `policy_obligation_ledger@1`, plus one tiny end-to-end ANM reference chain and minimal starter vocabulary/coexistence freeze sufficient for that chain | closed_on_main |
| `V47-B` | schema/example and vocabulary hardening | widened and hardened fact-kind / provenance vocabulary plus concrete ANM / fact-bundle / result-set / ledger examples | closed_on_main |
| `V47-C` | coexistence and companion-doc adoption lane | broader standalone-vs-companion posture, current-markdown coexistence rules, and bounded migration discipline beyond the `V47-A` minimum non-override freeze | planned_next_default_candidate |
| `V47-D` | selector / predicate ownership transition lane | later move from bootstrap string selectors and bootstrap contracts toward imported O-owned selectors and E-owned predicate registries | planned_later_not_selected_here |
| `V47-E` | downstream policy-bearing consumer seam | later consumers over descriptive, benchmark, or runtime artifact worlds using the released ANM substrate | planned_later_not_selected_here |

These output names are planning-level candidate names, not lock-level schema authority.

The `V47-C` through `V47-E` ladder should be read as provisional planning scaffolding.

If the released `V47-A` plus `V47-B` stack reveals that coexistence posture,
companion-doc adoption, or migration discipline is weaker or noisier than expected,
widening into later paths may need to pause, reorder, or narrow.

## Recommended Next Path (`V47-C`)

Implement the bounded coexistence and companion-doc adoption lane next.

`V47-C` should introduce:

- one canonical bounded standalone-vs-companion doctrine over the released `V47-A` +
  `V47-B` stack;
- one explicit non-override rule relative to current markdown lock/planning authority;
- one explicit companion embedding posture for readable markdown that contains
  authoritative `D@1` blocks without becoming a repo-wide migration mandate;
- one bounded migration discipline:
  - when companion posture is allowed;
  - when standalone posture is preferred;
  - when existing current-markdown authority remains controlling;
  - what may constrain a later migration decision without minting it;
- one explicit adoption boundary for later policy-bearing docs:
  - what the released ANM stack may constrain;
  - what still requires later authority or lock-level adoption;
- no widening yet into:
  - imported O-owned selector handles;
  - imported E-owned predicate registries;
  - source-level `DEFERRED`;
  - waiver or deferral issuance;
  - execution or approval authority.

`V47-C` remains adoption-first and non-executive:

- it may define how the released ANM stack coexists with current markdown doctrine;
- it may not yet authorize execution, mutation, scheduling, approval, or repo-wide
  markdown supersession by itself.

## Why This Path

- `V47-A` and `V47-B` are already closed, so the next unclosed gap is broader
  coexistence and companion-doc adoption doctrine rather than more substrate or example
  hardening.
- The released stack is now strong enough that coexistence can be made explicit without
  reopening ANM source syntax, `D-IR`, checker facts, result sets, or ledger state.
- The family still needs a bounded rule for how current markdown authority and ANM
  companion posture coexist before any later ownership transition or downstream consumer
  lane widens further.
- Doing this before `V47-D` or `V47-E` keeps adoption boundaries explicit and avoids
  smuggling migration or authority assumptions into selector/predicate ownership work or
  later consumers.

## First-Slice Boundary (`V47-C`)

`V47-C` should stay bounded to:

- coexistence/adoption doctrine only over the released ANM stack;
- standalone-vs-companion posture only;
- current-markdown non-override rule only;
- bounded migration discipline only;
- explicit allowed constrain actions only:
  - companion posture may coexist with current markdown authority;
  - released ANM artifacts may be referenced or embedded without automatic authority
    supersession;
  - later migration may be informed by released ANM hardening outputs but not minted by
    them automatically.

It should not attempt:

- repo-wide conversion of existing docs;
- imported O-owned selector handles;
- imported E-owned predicate registries;
- source-level `DEFERRED`;
- execution, approval, or mutation authority;
- broad downstream consumer integrations.

## Follow-On Paths Inside `V47`

### `V47-B`

Schema/example and vocabulary hardening lane, now closed on `main`:

- widened fact-kind and provenance vocabulary in bounded, typed ways;
- committed standalone, companion, clause-scope blocker, zero-match, and
  stale-row-reconciliation example families;
- retained authoritative/mirror schema parity and deterministic replay over the
  hardened example surface.

### `V47-C`

Coexistence and companion-doc adoption lane:

- widen coexistence doctrine beyond the `V47-A` minimum boundary by making explicit:
  - standalone-vs-companion posture;
  - relationship to current lock/planning markdown authority;
  - bounded migration discipline without repo-wide conversion.

### `V47-D`

Selector / predicate ownership transition lane:

- move beyond raw bootstrap string selectors where justified;
- introduce later O-owned selector-handle posture where justified;
- introduce later E-owned predicate-registry posture where justified;
- keep the first bounded artifact family stable while ownership moves outward.

### `V47-E`

Deferred downstream consumer seam:

- later family work may use the released ANM substrate to express policy-bearing rules
  over descriptive, benchmark, or runtime artifact worlds;
- that seam remains later and not selected by this planning draft.

## Candidate Package Ownership

Package ownership should remain planning-bound for now.

The first planning pass should therefore assume:

- no package-lock commitment selected yet;
- one likely bounded first owner may later be chosen, but it remains
  `not_selected_yet` at this planning stage.

This should be read as intentional restraint, not missing planning detail.

The family surface is stable enough to plan without freezing implementation-package
placement prematurely.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
- `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`
- `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
- `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
- `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`

Connected but non-authorizing context docs are:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`

Released earlier shaping surfaces that `V47` should learn from rather than reopen are:

- released `V41-A` through `V41-F`
- released `V45-A` through `V45-F`

## Planning Boundary

- no reopening of released `V41` or released `V45` contracts is authorized by this
  planning draft;
- no automatic supersession of the `V43`, `V44`, `V45`, or `V46` planning branches is
  authorized by this planning draft;
- no lock-level schema authority is created by the candidate artifact names above;
- no prose-obligation inference outside explicit `D@1` surfaces is authorized by this
  planning draft;
- no waiver or deferral authority is authorized by checker facts, result sets, or
  ledger rows alone;
- no mutation, scheduling, recursive execution, or approval authority is authorized by
  this planning draft;
- no repo-wide markdown migration is selected by this planning draft;
- no downstream policy-bearing consumer seam is selected by this planning draft beyond
  the bounded normative-compilation substrate itself.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v29.md",
  "baseline_arc": "vNext+107",
  "closed_prior_families": [
    "V41",
    "V42",
    "V45"
  ],
  "connected_candidate_families_in_scope": [
    "V43",
    "V44",
    "V45",
    "V46",
    "V47"
  ],
  "branch_candidate_family": "V47",
  "branch_candidate_status": "selected_for_v30_planning_surface_not_repo_wide_family_selection",
  "connected_families_not_reopened_here": [
    "V43",
    "V44",
    "V45",
    "V46"
  ],
  "closed_current_family_paths": [
    "V47-A",
    "V47-B"
  ],
  "planned_current_family_paths": [
    "V47-C",
    "V47-D",
    "V47-E"
  ],
  "default_next_arc_candidate_for_this_branch": "V47-C",
  "default_next_concrete_arc_candidate_for_this_branch": "vNext+108",
  "family_architecture_doc": "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md",
  "pre_lock_companion_docs_expected": [
    "docs/DRAFT_D1_DIALECT_SPEC_v0.md",
    "docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md",
    "docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md",
    "docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md",
    "docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md",
    "docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md"
  ],
  "planned_family_packages": [],
  "first_slice_active_packages": [],
  "package_selection_status": "not_selected_yet",
  "family_theme": "adeu_authoritative_normative_markdown_and_bounded_d1_compilation_substrate",
  "branch_local_planning_selection_only": true,
  "v45_complete_and_consumed_as_descriptive_substrate_only": true,
  "markdown_native_container_required": true,
  "authoritative_dialect_blocks_required": true,
  "no_prose_inference_required": true,
  "normalized_ir_required": true,
  "bootstrap_predicate_contracts_required": true,
  "fact_only_checker_posture_required": true,
  "checker_fact_bundle_required": true,
  "policy_evaluation_result_set_required": true,
  "policy_obligation_ledger_required": true,
  "v47a_tiny_reference_chain_required": true,
  "v47a_result_to_ledger_mapping_freeze_required": true,
  "v47a_minimal_checker_fact_kind_freeze_required": true,
  "v47a_minimal_provenance_mode_freeze_required": true,
  "v47a_minimal_coexistence_boundary_required": true,
  "v47a_non_executive_substrate_required": true,
  "v47b_schema_example_and_vocabulary_hardening_closed_on_main": true,
  "selector_zero_match_policy_required": true,
  "only_if_and_unless_semantics_required": true,
  "waiver_and_deferral_authority_initially_external_or_deferred": true,
  "repo_wide_migration_initially_deferred": true,
  "v47c_broader_companion_doc_and_coexistence_lane_planned": true,
  "v47d_selector_predicate_ownership_transition_deferred": true,
  "v47e_downstream_consumer_seam_not_selected_here": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md"
}
```
