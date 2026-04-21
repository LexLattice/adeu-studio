# Draft ADEU ANM Native Documentation Practice V66A Implementation Mapping v0

Status: support note for the `V66-A` starter implementation pass after the ANM
compiler substrate closed on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V66-A` slice should widen from the already released `V47` ANM substrate into one
repo-scale ANM source discovery / authority-profile / class-policy starter without
reopening `D@1` semantics, silently superseding current markdown authority, or
turning the whole repo into a hard-gated ANM corpus by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`
- `docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/anm.adeu.md`
- `docs/support/REVIEW_GPTPRO_V66_FAMILY_SELECTOR_v0.md`
- `docs/support/REVIEW_GPTPRO_V66A_STARTER_BUNDLE_v0.md`

## Carry Forward Nearly As-Is

- the released `V47-A` through `V47-F` ANM substrate:
  - explicit ANM source posture
  - explicit `D@1` blocks
  - typed D-AST
  - normalized `D-IR`
  - bootstrap predicate contracts
  - fact-only checker bundles
  - policy evaluation result sets
  - policy obligation ledgers
  - coexistence doctrine
  - selector / predicate ownership-transition doctrine
  - bounded policy-consumer bindings
- the rule that prose remains prose unless an explicit ANM authority block says
  otherwise
- the rule that current markdown remains controlling until explicit transition law
  says otherwise
- the rule that generated reader views are non-authoritative by default
- the rule that support docs may not overpromote into lock or planning authority
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

Candidate new starter surfaces:

- `anm_source_set_manifest@1`
- `anm_doc_authority_profile@1`
- `anm_doc_class_policy@1`

Those starter surfaces should remain bounded to:

- one discovered doc inventory only
- one governed ANM source set only
- one explicit source-posture and authority-profile layer only
- one explicit document-class policy layer only

They should decide only:

- which docs are inside the governed ANM source set here;
- how source classification axes stay distinct:
  - `doc_class`
  - `authority_layer`
  - `source_posture`
  - `lifecycle_status`
  - `classification_status`
- whether a companion posture is minimally registered here;
- whether a doc is allowed to emit the authority posture it claims under starter
  class policy.

They should keep:

- no new `D@1` semantics
- no new modal heads
- no new predicate or selector ownership doctrine
- no generated reader projection yet
- no semantic diff report yet
- no full migration binding profile yet
- no stable versioned compile report artifact yet
- no implicit supersession of current `.md` authority
- no hard-gating of plain historical/support markdown merely because it exists

`V66-A` should keep explicit:

- `discovered_doc_inventory` is not the same thing as `governed_anm_source_set`
- `.adeu.md` presence is not supersession by itself
- companion presence is not supersession by itself
- minimal companion registration is allowed in `V66-A`
- full migration binding is deferred to `V66-B`
- ephemeral CLI diagnostics are allowed in `V66-A`
- stable `anm_compile_report@1` remains deferred to `V66-C`
- doc authority profile is metadata posture, not implementation law by itself
- class policy is document-governance law, not runtime behavior by itself

For `V66-A`, this starter axis split controls over any earlier family-level prose
that treated `historical`, `generated`, or `unknown` as flat document classes.

Starter enum set:

- `doc_class`:
  - `lock`
  - `architecture`
  - `planning`
  - `support`
  - `non_governance`
- `authority_layer`:
  - `lock`
  - `architecture`
  - `planning`
  - `support`
  - `none`
- `source_posture`:
  - `legacy_markdown`
  - `standalone_anm`
  - `companion_anm`
  - `generated_projection`
- `lifecycle_status`:
  - `living`
  - `historical`
  - `superseded`
  - `draft`
  - `generated`
- `classification_status`:
  - `classified`
  - `unknown_requires_registration`
  - `excluded_non_governance`

## Starter Field Direction

Minimum `anm_source_set_manifest@1` direction:

- top-level:
  - `schema_id`
  - `manifest_id`
  - `source_entries`
- each source entry:
  - `doc_ref`
  - `doc_id_or_none`
  - `doc_class`
  - `authority_layer`
  - `source_posture`
  - `lifecycle_status`
  - `classification_status`
  - `content_hash`
  - `profile_ref_or_none`
  - `host_doc_ref_or_none`
  - `companion_registration_status_or_none`
  - `generated_from_ref_or_none`

Minimum `anm_doc_authority_profile@1` direction:

- `schema_id`
- `doc_id`
- `doc_ref`
- `doc_class`
- `authority_layer`
- `source_posture`
- `lifecycle_status`
- `allowed_authority_blocks`
- `allowed_outputs`
- `forbidden_outputs`
- `current_markdown_authority_relation`
- `allowed_consumers`
- `requires_transition_law_for_supersession`

Minimum `anm_doc_class_policy@1` direction:

- `schema_id`
- one policy row per `doc_class`
- each row should carry:
  - `allowed_authority_layers`
  - `allowed_source_postures`
  - `allowed_authority_blocks`
  - `allowed_outputs`
  - `forbidden_outputs`
  - `hard_gates`
  - `warning_gates`

Authority-profile source precedence for `V66-A`:

1. explicit ANM profile block, when present;
2. source-set manifest entry, when the document is registered there;
3. deterministic compiler classification, only for mechanically derivable fields
   such as `doc_ref` and `source_posture`.

Front matter may assist discovery, but:

- it does not mint obligations;
- it does not outrank an explicit profile block;
- it does not outrank a registered manifest entry.

If multiple profile sources exist, they must agree.
Contradictory profile sources fail closed.

Deterministic inventory rules for `V66-A`:

- `content_hash`:
  - `sha256` of raw file bytes as read from disk
- `doc_ref`:
  - repo-relative POSIX path
- inventory order:
  - sorted by `doc_ref` ascending
- timestamps:
  - excluded from starter semantic content
- recommended ignored crawl paths:
  - `.git/`
  - `.venv/`
  - `node_modules/`
  - `__pycache__/`
  - generated caches that are not committed docs

## Starter Source-Set Entry Rule

A doc enters the governed ANM source set here only if:

- it has a `.adeu.md` extension; or
- it is registered as a companion overlay; or
- it contains a recognized ANM authority block; or
- it is listed in the source-set manifest; or
- a later lock explicitly opts it into `V66` validation.

Only compiler-recognized authority zones count for this entry rule.

The following do not opt a doc into the governed ANM source set by themselves:

- code-fenced examples of `D@1`
- quoted examples
- escaped examples
- prose discussion of `D@1` or ANM posture

Plain support or historical markdown should not become hard-gated starter ANM source
merely because it is present in the repo.

## Do Not Import

- broader migration-binding doctrine
- generated reader projection doctrine
- semantic diff doctrine
- prose-boundary notice doctrine
- stable compile-report artifact doctrine
- new `D@1` language widening
- support-doc overpromotion
- repo-wide `.adeu.md` rename posture
- silent markdown supersession

## EntryPoint Posture

Starter entrypoints such as repo-scale inventory and check commands are validation
surfaces, not runtime API surfaces.

`V66-A` may emit ephemeral CLI diagnostics and test assertions through those
entrypoints, but it does not yet commit a stable versioned `anm_compile_report@1`
artifact.
