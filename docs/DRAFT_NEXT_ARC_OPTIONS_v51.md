# Draft Next Arc Options v51

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v50.md`, now that the
`V62` through `V65` multi-arc branch is closed on `main`, and after support-layer
review of `docs/support/anm.adeu.md`.

Authority layer: planning.

This draft does not automatically supersede the connected planning branches in
`docs/DRAFT_NEXT_ARC_OPTIONS_v42.md` through `docs/DRAFT_NEXT_ARC_OPTIONS_v50.md`.
Those branches remain the canonical planning records for the already closed `V59`
through `V65` families.

Instead, this draft records the next connected candidate family after the completed
`V62` through `V65` roadmap:

how should ADEU turn the already released ANM / `D@1` substrate into a repo-native
documentation practice by authority layer, with explicit source discovery,
document-class policy, companion migration, and reader projections, without
reopening the closed `V47` language/compiler ladder, inferring policy from prose,
silently superseding current markdown authority, or flattening lock, architecture,
planning, support, and historical docs into one authority class?

This is a planning document only. It is not a lock doc and does not authorize
runtime behavior, schema release, migration supersession, or implementation by
itself.

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

- the `V62` through `V65` multi-arc roadmap is closed on `main`:
  - `V62-A` through `V62-C` closed on `main`
  - `V63-A` through `V63-C` closed on `main`
  - `V64-A` through `V64-C` closed on `main`
  - `V65-A` through `V65-C` closed on `main`
- `V47-A` through `V47-F` are already closed on `main` and remain the released
  ANM / `D@1` bootstrap substrate recorded in
  `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md`:
  - explicit ANM source posture
  - explicit `D@1` authority blocks
  - `d1_normalized_ir@1`
  - bootstrap predicate contracts
  - fact-only checker bundles
  - policy evaluation result sets
  - policy obligation ledger projection
  - coexistence and companion posture
  - selector / predicate ownership-transition posture
  - bounded policy-consumer bindings
- the repo already has the main ANM shaping references on `main`:
  - `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
  - `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
  - `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
  - `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`
  - `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
  - `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
  - `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
  - `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v0.md`
  - `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`
  - `docs/support/anm.adeu.md`
- the repo also already has the relevant package substrate on `main`:
  - `packages/adeu_semantic_source`
  - `packages/adeu_commitments_ir`
  - `packages/adeu_semantic_compiler`

## Gap

The repo no longer lacks the bounded ANM / `D@1` source and compiler substrate.

`V47` already shipped the lower-level constitutional pieces on `main`:

- explicit bounded authority blocks inside markdown;
- normalized semantic lowering;
- fact-only checker posture;
- evaluator and ledger separation;
- coexistence and companion posture;
- bounded ownership and consumer bindings.

The repo still lacks the repo-scale adoption layer that would make ANM a native
documentation practice rather than a bounded released substrate plus fixtures.

In particular, the repo still lacks:

- one repo-scale ANM source discovery and inventory posture across living,
  historical, companion, and generated documentation surfaces;
- one explicit document authority profile per ANM-bearing doc so:
  - doc class,
  - authority layer,
  - source posture,
  - allowed block kinds, and
  - allowed consumers
  are machine-visible rather than implied by filename and prose;
- one machine-checkable document-class policy so lock, architecture, planning,
  support, and historical docs do not silently collapse into one authority class;
- one standardized migration-binding and companion-registration path so existing
  `.md` docs are not silently superseded by nearby `.adeu.md` overlays;
- one generated reader-view / semantic-diff posture that makes ANM practical for
  daily review without minting new authority out of generated prose; and
- later one advisory hardening seam over the same ANM-native source set so drift,
  overpromotion, stale generated views, and ambiguous migration posture are visible
  without being mistaken for runtime or release authority.

The starter slice should also keep the source-set boundary explicit:

- `discovered_doc_inventory`:
  - all docs noticed by repo crawling
- `governed_anm_source_set`:
  - docs that are:
    - `.adeu.md` sources,
    - registered companion overlays,
    - docs containing recognized ANM authority blocks, or
    - docs explicitly opted into `V66` validation by manifest or later lock

Plain historical or support markdown should not become a hard-gated ANM source
merely because it exists in the repo.

So the repo still lacks the next documentation-governance fill that would let it
say:

- this exact ANM source set is the governed source set here;
- this exact document class and authority profile is the only controlling context
  for this source;
- this exact companion posture is registered and non-overriding unless later lock
  law says otherwise; and
- ANM-native practice remains explicit, replayable, and fail-closed rather than a
  prose-interpretation or filename-convention culture.

## Relationship To `V47`, `V59` Through `V65`, And Current Markdown Authority

`V47` asks:

- how should bounded ANM authority blocks compile, evaluate, and project into
  obligation-state artifacts without laundering authority out of prose, checker
  facts, results, or ledgers?

`V59` through `V65` ask:

- how should ADEU govern continuity, continuation, communication, transport/control
  surfaces, repo-bound writable authority, and delegated worker execution widening?

This new family asks:

- how should the already released ANM substrate become a repo-native documentation
  practice by authority layer?
- how should living docs adopt `.adeu.md` or companion ANM posture without making
  all docs full normative syntax?
- how should current markdown remain controlling until explicit transition law says
  otherwise?
- how should generated reader views and semantic diffs support daily authoring and
  review without becoming new authority sources?

So this family may constrain:

- ANM source discovery and classification;
- document-class-specific authority posture;
- companion registration and migration posture;
- generated reader-view and semantic-diff discipline;
- repo-native ANM authoring / validation workflow.

But it may not mint:

- new `D@1` modal or assertion semantics already owned by `V47`;
- new selector ownership or predicate-registry doctrine already bounded in `V47-D`;
- new policy-consumer bindings already bounded in `V47-E` / `V47-F`;
- runtime, release, or schema authority from generated reader views;
- implicit supersession of current `.md` authority by filename or proximity alone;
- LLM-inferred obligations from prose;
- repo-wide mandatory `.adeu.md` renaming by default; or
- reopening of `V62` through `V65` runtime families.

Ordering discipline for this branch:

- `V47` remains the owner of ANM source-language, normalized IR, checker, evaluator,
  and ledger substrate;
- `V59` through `V65` remain closed runtime / execution families on `main`;
- this new family would own only the repo-scale ANM adoption and documentation
  practice layer on top of the closed `V47` substrate.

## Recommended Family

- family name: `V66`
- family theme: authority-layered ANM-native documentation practice
- lineage role:
  - `packages/adeu_semantic_source` remains the ANM authoring and source-lowering
    home
  - `packages/adeu_commitments_ir` remains the schema / model home for emitted
    ANM-side artifacts
  - `packages/adeu_semantic_compiler` remains the deterministic orchestration home
  - current markdown docs remain source-of-truth unless an explicit migration law
    changes that posture
- family role:
  - one repo-scale ANM source-set and document-authority starter
  - later one migration / reader-projection and semantic-diff lane
  - later one advisory adoption hardening lane
- first-family discipline:
  - ANM-native by authority layer, not repo-wide rename by default
  - prose remains prose
  - only explicit authority blocks compile
  - front matter and generated reader prose do not mint obligations by themselves
  - companion overlays remain non-overriding by default
  - lock / architecture / planning / support / historical classes remain distinct
  - current `.md` authority remains explicit until a later lock-level transition
    says otherwise

## Recommended Next Slice

- family remains: `V66`
- next concrete slice: `V66-A`
- recommended selector outcome:
  - keep `V47` closed on `main` as the ANM compiler and evaluation substrate
  - keep current markdown authority explicit on `main`
  - select `V66-A` as the next default candidate

Default next-slice posture:

- consume the shipped `V47` substrate intact:
  - `D@1` extraction remains unchanged
  - normalized `D-IR` remains unchanged
  - predicate contracts remain unchanged
  - fact bundles / result sets / ledgers remain unchanged
  - coexistence doctrine remains consumed, not reopened
- add one repo-scale source-discovery and class-policy starter only:
  - `anm_source_set_manifest@1`
  - `anm_doc_authority_profile@1`
  - `anm_doc_class_policy@1`
- keep `V66-A` bounded to inventory and policy posture:
  - detect `.adeu.md` sources
  - detect registered companions
  - distinguish:
    - `doc_class`
    - `authority_layer`
    - `source_posture`
    - `lifecycle_status`
    - `classification_status`
  - classify the governed ANM source set separately from the broader discovered
    doc inventory
  - reject unregistered companions
  - reject supersession claims without explicit lock-level transition law
- keep `V66-A` companion posture minimal and bounded:
  - `V66-A` may carry minimal host / companion registration fields inside
    `anm_source_set_manifest@1` and `anm_doc_authority_profile@1`
  - `V66-A` does not emit the full `anm_migration_binding_profile@1`
  - `V66-B` later widens the registered companion relation into the full migration
    binding profile
- keep the starter slice fail-closed:
  - malformed authority profile fails closed
  - contradictory doc-class posture fails closed
  - contradictory host / companion linkage fails closed
  - unknown governance-bearing doc classification remains explicit rather than
    defaulting silently
- keep authority boundaries explicit:
  - source discovery is not supersession law
  - document authority profile is not implementation authority by itself
  - class policy is not runtime behavior by itself
  - support-layer ANM awareness is not lock promotion
- keep later widening deferred:
  - generated reader projections deferred to `V66-B`
  - semantic diff reports deferred to `V66-B`
  - migration binding profile deferred to `V66-B`
  - prose-boundary notices, selector-resolution bundles, and advisory adoption
    hardening deferred to `V66-C`
  - no new `D@1` language widening selected here

## Suggested `V66` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V66-A` | source discovery / class policy starter | `anm_source_set_manifest@1`, `anm_doc_authority_profile@1`, and `anm_doc_class_policy@1` over one governed repo ANM source set only | selected next path |
| `V66-B` | migration / reader projection | `anm_migration_binding_profile@1`, `anm_reader_projection_manifest@1`, and `anm_semantic_diff_report@1` over the same governed source set only | prepared later |
| `V66-C` | advisory adoption hardening | `anm_compile_report@1`, `anm_prose_boundary_notice_set@1`, and related adoption hardening outputs over the same governed source set only | prepared later |

These output names are planning-level candidate names, not lock-level schema
commitments yet.

## Recommended Bundle

- current selector doc:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`
- next family architecture doc:
  - likely `docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`
- next family support mapping:
  - likely `docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md`
