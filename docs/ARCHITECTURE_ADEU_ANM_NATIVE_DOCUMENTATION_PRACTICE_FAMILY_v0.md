# Architecture ADEU ANM Native Documentation Practice Family v0

Status: planning / decomposition draft.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended family
shape for `V66` downstream of the already closed `V47` ANM substrate.

## 1. Family Thesis

`V66` should not be read as “ANM again.”

`V47` already closed the bounded ANM / `D@1` language and compiler substrate on
`main`.

`V66` is the downstream adoption family that asks:

- how should ANM become native repo practice for living governance-bearing docs?
- how should that practice remain explicit by authority layer?
- how should current `.md` authority remain controlling until explicit transition
  law says otherwise?
- how should ANM improve daily authoring and review without turning the whole repo
  into rigid formal syntax?

The intended end-state is:

- ANM-first for living governance-bearing docs
- companion ANM during migration
- plain markdown for non-governance and historical prose

That is not a repo-wide rename doctrine.
It is an authority-layered adoption doctrine.

## 2. Relationship To `V47`

`V47` remains the owner of:

- `D@1` block extraction
- typed D-AST
- normalized `D-IR`
- bootstrap predicate contracts
- checker fact bundles
- policy evaluation result sets
- policy obligation ledger
- coexistence posture
- selector / predicate ownership-transition posture
- policy consumer bindings

`V66` should consume those released surfaces.
It should not reopen them casually.

So `V66` may constrain:

- source-set discovery
- source posture
- document-class authority posture
- migration binding
- generated reader projections
- semantic diff posture
- repo-native ANM workflow

But it may not mint:

- new ANM clause semantics by default
- new modal heads by default
- new predicate or selector ownership rules by default
- policy from prose
- supersession by filename alone

## 3. Family Role

`V66` should own the repo-scale documentation practice layer that sits above the
closed `V47` substrate.

That means it should make the following machine-visible:

1. which docs are ANM-bearing
2. which docs are lock / architecture / planning / support / historical
3. whether a source is standalone ANM or companion ANM
4. whether a companion is registered and non-overriding
5. whether generated reader views or semantic diffs are current
6. whether a doc is allowed to emit the authority posture it claims

The family is therefore about documentation governance and migration structure, not
runtime governance.

## 4. Source Model

The repo-scale source model should have three planes:

1. Prose plane
   - ordinary markdown
   - human explanation
   - rationale
   - examples
   - caveats
   - non-authoritative summaries
2. Authority-zone plane
   - explicit compiler-recognized blocks only
   - `D@1` where selected
   - later doc-profile / planning-boundary / migration-binding / seam-map blocks
3. Derived deterministic plane
   - IR
   - profiles
   - manifests
   - reader projections
   - semantic diffs
   - compile reports

The central anti-laundering rule remains:

- prose remains prose unless an explicit ANM authority block says otherwise

The source classification model should also keep its axes separate.

Recommended starter separation:

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

The family should not collapse those axes into one flat “doc type” vocabulary.

The repo-scale discovery posture should also distinguish:

- `discovered_doc_inventory`
  - everything the crawler notices
- `governed_anm_source_set`
  - docs that are actually under `V66` ANM validation posture

That lets the starter slice inventory the broader corpus without making every
historical markdown file a hard-gated ANM source.

## 5. Document-Class Policy

`V66` should keep the document classes distinct.

### 5.1 Lock docs

- highest-density ANM target
- new living lock docs may later default to `.adeu.md`
- existing `.md` locks remain controlling until explicit transition law
- generated artifacts may include IR, profiles, semantic diffs, and reader views

### 5.2 Architecture / decomposition docs

- gradual ANM adoption
- sparse authority zones
- seam maps and anti-overpromotion boundaries matter more than dense normative
  clauses
- architecture docs do not become lock substitutes by implication

### 5.3 Planning docs

- mixed mode
- selected active planning docs may become `.adeu.md` or use companions
- planning should gain structured boundaries first, not dense normative lowering
- planning guards remain planning guards unless promoted by lock

### 5.4 Support docs

- usually stay plain `.md`
- optional ANM posture only when support semantics are reusable and explicitly
  worth compiling
- support docs may not overpromote into lock or planning authority

### 5.5 Historical docs

- usually remain as-is
- may gain non-overriding companion overlays
- may not be silently rewritten into new authority

## 6. Family Surfaces

The family should widen through explicit repo-scale surfaces rather than informal
convention.

Candidate surface set:

| Surface | Role |
|---|---|
| `anm_source_set_manifest@1` | enumerates governed ANM sources, hosts, companions, and status |
| `anm_doc_authority_profile@1` | records doc class, authority layer, source posture, allowed blocks, and current authority relation |
| `anm_doc_class_policy@1` | records what each document class may emit and what failures are hard gates |
| `anm_migration_binding_profile@1` | records host / overlay migration relation and non-override posture |
| `anm_reader_projection_manifest@1` | records generated reader views and drift state |
| `anm_semantic_diff_report@1` | records semantic additions, removals, and authority-surface changes |
| `anm_compile_report@1` | records repo-scale compilation and validation diagnostics |
| `anm_prose_boundary_notice_set@1` | warning-only notices for prose that reads normatively but is not compiled |

`V66-A` should not ship all of these at once.
They are the family-level target set.

For the starter slice, the first three surfaces should have only bounded minimum
shape.

Minimum `anm_source_set_manifest@1` direction:

- source entries should carry:
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

- each profile should carry:
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

- class-policy rows should carry:
  - `doc_class`
  - `allowed_authority_layers`
  - `allowed_source_postures`
  - `allowed_authority_blocks`
  - `allowed_outputs`
  - `forbidden_outputs`
  - `hard_gates`
  - `warning_gates`

## 7. Non-Equivalence And Non-Generalization Rules

The family should say these lines directly:

- `.adeu.md` presence is not supersession by itself
- companion presence is not supersession by itself
- generated reader view is not authority by itself
- front matter is not obligation by itself
- support-layer ANM awareness is not lock law by itself
- planning-layer scope guard is not lock prohibition by itself
- ANM-native practice is not a repo-wide rename requirement by default

These are the constitutional anti-laundering lines for the family.

## 8. Slice Ladder

### `V66-A` — source discovery / class policy starter

Own:

- governed source inventory
- source posture classification
- document authority profiles
- document-class policy
- fail-closed classification and companion registration checks

Bounded companion rule:

- `V66-A` may carry minimal host / companion registration fields inside the source
  manifest and authority profile
- `V66-A` does not yet emit the full migration-binding profile
- `V66-B` later upgrades the already registered relation into explicit
  `anm_migration_binding_profile@1`

Do not own yet:

- generated reader views
- semantic diffs
- migration binding profiles
- advisory prose-boundary lint

### `V66-B` — migration / reader projection

Own:

- migration binding profile
- reader projection manifest
- semantic diff report
- non-authoritative generated reader-view discipline

Do not own yet:

- advisory adoption hardening
- broader selector / predicate widening

### `V66-C` — advisory adoption hardening

Own:

- compile report
- prose-boundary notice set
- advisory drift and overpromotion visibility

Remain advisory only:

- no new source authority by itself
- no new transition law by itself
- no runtime or release authority by itself

## 9. Implementation Posture

The family should primarily touch:

- `packages/adeu_semantic_source`
- `packages/adeu_commitments_ir`
- `packages/adeu_semantic_compiler`
- selected doc fixtures and support examples

The family should not start by rewriting the live doc corpus wholesale.

The correct order is:

1. classify and inventory
2. make document authority explicit
3. add migration and reader projections
4. harden advisory adoption posture
5. only then widen actual doc-base migration aggressively
