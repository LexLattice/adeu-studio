## Verdict

The three-doc bundle is **directionally strong and consistent with the architecture proposed above**. I would keep `V66` as the next implementation family and keep the `V66-A / V66-B / V66-C` ladder.

I would **not** treat the bundle as implementation-ready yet. It is ready as a **planning / decomposition / support shaping bundle**, but the first lock should not be drafted until a few boundary issues are tightened.

The strongest parts are:

* `V66` is correctly framed as **downstream adoption practice**, not “ANM again” or a reopening of `V47`. The architecture doc explicitly leaves `D@1`, D-AST, D-IR, predicate contracts, fact bundles, result sets, ledgers, coexistence, ownership transition, and consumer bindings under `V47`. 
* `DRAFT_NEXT_ARC_OPTIONS_v51.md` correctly identifies the actual gap: the repo has the bounded ANM / `D@1` substrate, but lacks the repo-scale adoption layer: source inventory, authority profiles, class policy, companion migration posture, reader views, and semantic diff discipline. 
* The implementation mapping has the right package split: `adeu_semantic_source` for source/companion/profile helpers, `adeu_commitments_ir` for models and schemas, and `adeu_semantic_compiler` for repo-scale orchestration. 

My review result:

> **Approve the family direction. Revise before locking `V66-A`. Do not implement from these docs alone without a starter lock.**

---

## High-level review

### What is working well

The bundle preserves the core anti-laundering posture. The architecture doc says the source model has a prose plane, an explicit authority-zone plane, and a derived deterministic plane, and repeats the central rule that prose remains prose unless an explicit ANM authority block says otherwise. 

The bundle also correctly rejects the dangerous migration paths:

* no repo-wide rename doctrine
* no silent `.md` supersession
* no generated-reader-view authority
* no front-matter-as-obligation
* no planning/support overpromotion
* no new `D@1` semantics in the starter slice

Those lines are stated especially clearly in the architecture doc’s “Non-Equivalence And Non-Generalization Rules.” 

The `V66-A` starter slice is also appropriately bounded. `DRAFT_NEXT_ARC_OPTIONS_v51.md` selects only `anm_source_set_manifest@1`, `anm_doc_authority_profile@1`, and `anm_doc_class_policy@1` for the first slice, while deferring reader projections, semantic diffs, migration binding profiles, prose-boundary notices, selector-resolution bundles, and broader advisory hardening. 

That is the right implementation posture.

---

## Main issues to fix before the first lock

### 1. Separate `doc_class`, `authority_layer`, `source_posture`, and lifecycle status

This is the most important correction.

The implementation mapping currently says `V66-A` should classify docs into:

```text
lock
architecture
planning
support
historical
generated
unknown
```

That conflates different axes. `lock`, `architecture`, `planning`, and `support` are authority/document classes. `historical` is lifecycle status. `generated` is source/projection posture. `unknown` is a validation state. 

This matters because collapsing those axes risks recreating the flat authority model the family is explicitly trying to avoid.

Use this instead:

```yaml
doc_class:
  enum:
    - lock
    - architecture
    - planning
    - support
    - non_governance

authority_layer:
  enum:
    - lock
    - architecture
    - planning
    - support
    - none

source_posture:
  enum:
    - legacy_markdown
    - standalone_anm
    - companion_anm
    - generated_projection

lifecycle_status:
  enum:
    - living
    - historical
    - superseded
    - draft
    - generated

classification_status:
  enum:
    - classified
    - unknown_requires_registration
    - excluded_non_governance
```

That one edit would make the family much more implementation-safe.

### 2. Clarify how `V66-A` can reject companions while deferring migration binding profiles

The current ladder says `V66-A` does **not** own `anm_migration_binding_profile@1`, but the implementation mapping also says `V66-A` should reject unregistered companions, contradictory host/companion linkage, and supersession claims without transition law.  

That is not fatal, but it needs one sentence of clarification.

Recommended rule:

```text
V66-A owns minimal companion registration fields inside
anm_source_set_manifest@1 and anm_doc_authority_profile@1.

V66-A does not emit the full anm_migration_binding_profile@1.

V66-B enriches the already-registered companion relation into the full
migration-binding profile.
```

Without that clarification, reviewers may ask why a deferred `V66-B` surface is required for `V66-A` checks.

### 3. Define the governed source-set boundary

The docs say `V66-A` should discover `.adeu.md` sources, registered companions, and classify docs. That is right, but the repo has a large existing Markdown corpus. The first implementation slice must not accidentally turn every Markdown file into a CI liability.

Add this distinction:

```text
discovered_doc_inventory:
  all docs noticed by the scanner

governed_anm_source_set:
  docs that are ANM-bearing, registered as companions, or explicitly opted into
  V66 validation
```

Then define the trigger rules:

```text
A document enters the governed ANM source set if:
- it has a .adeu.md extension;
- it is registered as a companion overlay;
- it contains a recognized ANM authority block;
- it is listed in the source-set manifest; or
- a lock explicitly opts it into V66 validation.
```

Plain historical/support Markdown should not fail CI merely because it exists.

### 4. Add minimum field shapes for the three `V66-A` artifacts

The current mapping names the correct artifacts, but does not yet say what fields they minimally contain. That is fine for a support draft, but the starter lock will need field-level commitments.

For `V66-A`, define only the minimum.

#### `anm_source_set_manifest@1`

```yaml
schema_id: anm_source_set_manifest@1
manifest_id: string
source_entries:
  - doc_ref: string
    doc_id: string | null
    doc_class: enum
    authority_layer: enum
    source_posture: enum
    lifecycle_status: enum
    classification_status: enum
    content_hash: string
    profile_ref: string | null
    host_doc_ref: string | null
    companion_registration_status: enum | null
    generated_from_ref: string | null
```

Avoid nondeterministic timestamps in the core manifest unless they are explicitly excluded from semantic hashing.

#### `anm_doc_authority_profile@1`

```yaml
schema_id: anm_doc_authority_profile@1
doc_id: string
doc_ref: string
doc_class: enum
authority_layer: enum
source_posture: enum
lifecycle_status: enum
allowed_authority_blocks:
  - string
allowed_outputs:
  - string
forbidden_outputs:
  - string
current_markdown_authority_relation: enum
allowed_consumers:
  - string
requires_transition_law_for_supersession: boolean
```

Important: this profile is a **metadata authority profile**, not an obligation ledger and not implementation authority.

#### `anm_doc_class_policy@1`

```yaml
schema_id: anm_doc_class_policy@1
policies:
  - doc_class: enum
    allowed_authority_layers:
      - enum
    allowed_source_postures:
      - enum
    allowed_authority_blocks:
      - string
    allowed_outputs:
      - string
    forbidden_outputs:
      - string
    hard_gates:
      - string
    warning_gates:
      - string
```

This gives the implementation enough shape without widening `D@1`.

### 5. Add an explicit class-policy matrix

The docs currently describe class policy in prose. That is good, but the lock will need a machine-checkable matrix.

Recommended starter matrix:

| Doc class        | May be `.adeu.md` | May have companion | May emit V47 D-IR from explicit D blocks | May emit lock obligation ledger | Must reject overpromotion |
| ---------------- | ----------------: | -----------------: | ---------------------------------------: | ------------------------------: | ------------------------: |
| `lock`           |               yes |                yes |                                      yes |   yes, when explicitly selected |                       yes |
| `architecture`   |               yes |                yes |                yes, sparse/explicit only |  no, unless later lock binds it |                       yes |
| `planning`       |               yes |                yes |                   yes, scope guards only |                              no |                       yes |
| `support`        |          optional |                yes |                        rare/support-only |                              no |                       yes |
| `non_governance` |     no by default |      no by default |                                       no |                              no |                       yes |

This keeps the existing document-class doctrine operational rather than rhetorical.

### 6. Clarify package responsibility boundaries

The implementation mapping is directionally right, but I would sharpen it:

```text
adeu_semantic_source:
  file-level ANM extraction and parsing
  authority-profile block parsing
  companion profile parsing
  source-level diagnostics

adeu_commitments_ir:
  Pydantic/dataclass models
  JSON schemas
  schema export parity
  fixture validation

adeu_semantic_compiler:
  repo crawling
  source-set manifest construction
  class-policy application
  cross-document companion validation
  artifact emission
  CI entrypoints
```

Do not put repo-wide crawling too deeply inside `adeu_semantic_source`; keep that package mostly source-local.

### 7. Add missing shaping references

`DRAFT_NEXT_ARC_OPTIONS_v51.md` correctly names the intent-horizon glossary, authority-layering note, and future-seam promotion rules as interpretive doctrine. 

The architecture and implementation mapping should also list those as shaping inputs, especially because `V66` is fundamentally about authority-layer separation and migration/promotion law.

Add to the implementation mapping’s shaping inputs:

```text
docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md
docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md
docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md
docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md
```

The mapping already lists the main ANM specs and source seeds, which is good. 

### 8. Resolve the `anm_compile_report@1` timing issue

The mapping defers `anm_compile_report@1` to `V66-C`, but `V66-A` still needs some way to report diagnostics from `make anm-check` / `make anm-inventory`. 

Recommended clarification:

```text
V66-A may emit ephemeral CLI diagnostics and test assertion outputs.

V66-A does not commit a versioned anm_compile_report@1 artifact.

The stable, schema-governed compile report is deferred to V66-C.
```

That keeps the slice bounded without making `V66-A` unusable.

---

## Per-document review

### `DRAFT_NEXT_ARC_OPTIONS_v51.md`

This is the strongest of the three as a selector/planning doc.

It does the important things correctly:

* states that `V47` already shipped the ANM / `D@1` substrate;
* defines the remaining gap as repo-scale adoption practice;
* preserves current Markdown authority until explicit transition law;
* selects `V66-A` as the next candidate;
* defers generated views, semantic diffs, migration profiles, prose-boundary notices, selector-resolution bundles, and `D@1` widening. 

Recommended edits:

1. Add the four-axis classification model: `doc_class`, `authority_layer`, `source_posture`, `lifecycle_status`.
2. Add one paragraph saying `V66-A` governs a selected ANM source set, not the entire Markdown corpus by default.
3. Replace “likely” in the recommended bundle once the files are actually selected for commit.
4. Add explicit non-goal: `V66-A does not produce generated reader views or semantic diffs`.

Overall: **keep with minor-to-medium revisions.**

### `ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`

This is a good family architecture doc. It preserves the right thesis: `V66` is not a repo-wide rename and not a reopening of `V47`; it is an authority-layered adoption doctrine. 

Recommended edits:

1. Add a “Classification Axes” section after the source model.
2. Add a “V66-A Minimal Companion Registration vs V66-B Migration Binding” section.
3. Add a concrete class-policy matrix.
4. Add failure posture:

   * malformed profile
   * unregistered companion
   * host missing
   * host hash drift
   * support/planning overpromotion
   * generated view claiming authority
5. Add explicit note that front matter may help discovery, but the compiler should prefer a typed profile block or manifest entry for authority profile data.

Overall: **good architecture draft, but still too prose-level for lock handoff.**

### `DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md`

This is the right support mapping. It names the correct packages, artifact family, CLI candidates, fixture categories, and non-goals. 

Recommended edits:

1. Split source-local and repo-scale responsibilities more sharply.
2. Replace the class list with four-axis classification.
3. Add exact fixture paths, for example:

```text
packages/adeu_semantic_source/tests/fixtures/v66a/
  standalone_lock_profile.adeu.md
  registered_companion_overlay.adeu.md
  reject_orphaned_companion.adeu.md
  reject_supersession_without_transition.adeu.md
  reject_generated_view_claims_authority.adeu.md
  planning_boundary_profile.adeu.md
  support_non_overpromotion.adeu.md

packages/adeu_commitments_ir/tests/fixtures/v66a/
  reference_anm_source_set_manifest.json
  reference_anm_doc_authority_profile.json
  reference_anm_doc_class_policy.json
  reject_doc_class_status_conflation.json
  reject_forbidden_output_by_doc_class.json
```

4. Add schema filenames:

```text
packages/adeu_commitments_ir/schema/anm_source_set_manifest.schema.json
packages/adeu_commitments_ir/schema/anm_doc_authority_profile.schema.json
packages/adeu_commitments_ir/schema/anm_doc_class_policy.schema.json
```

5. Add exact CLI behavior:

```bash
make anm-inventory   # emits or validates source-set manifest
make anm-check       # parses profiles and class policy, fail-closed
make anm-compile     # optional wrapper; no V66-B/C artifacts yet
```

Overall: **good implementation scaffold, but it needs schema and test specificity before a starter lock.**

---

## Suggested insertion: classification section

I would add this to both the architecture doc and the implementation mapping.

```markdown
## Classification Axes

`V66` must not classify documentation through one flat enum.

Every governed source entry has at least four independent axes:

| Axis | Meaning |
|---|---|
| `doc_class` | The kind of document: `lock`, `architecture`, `planning`, `support`, or `non_governance`. |
| `authority_layer` | The authority layer the document may speak from: `lock`, `architecture`, `planning`, `support`, or `none`. |
| `source_posture` | The source shape: `legacy_markdown`, `standalone_anm`, `companion_anm`, or `generated_projection`. |
| `lifecycle_status` | The lifecycle state: `living`, `historical`, `superseded`, `draft`, or `generated`. |

`historical`, `generated`, and `unknown` are not document authority classes.

A generated reader view of a lock document is not itself a lock document.
A historical planning document remains planning-class unless explicitly reclassified.
An unknown classification is a validation state, not a fallback authority layer.
```

That section would prevent a lot of downstream ambiguity.

---

## Suggested insertion: `V66-A` companion clarification

```markdown
## `V66-A` Companion Registration Boundary

`V66-A` may validate minimal companion registration through
`anm_source_set_manifest@1` and `anm_doc_authority_profile@1`.

For `V66-A`, the required companion facts are only:

- `overlay_doc_ref`
- `host_doc_ref`
- `source_posture: companion_anm`
- `current_markdown_authority_relation`
- `overlay_authority_relation`
- `requires_transition_law_for_supersession`

`V66-A` does not emit the full `anm_migration_binding_profile@1`.

`V66-B` owns the richer migration-binding profile, including drift state,
semantic-diff relation, generated projection relation, and explicit transition
surface metadata.
```

This preserves the current ladder while making `V66-A` implementable.

---

## Suggested insertion: `V66-A` acceptance gates

```markdown
## `V66-A` Acceptance Gates

The starter slice is accepted only if:

1. `anm_source_set_manifest@1`, `anm_doc_authority_profile@1`, and
   `anm_doc_class_policy@1` have package-owned models and exported schemas.
2. Schema mirrors, if used, are deterministic and parity-checked.
3. Existing `V47-A` through `V47-F` fixtures remain green.
4. At least one standalone ANM fixture is classified correctly.
5. At least one registered companion fixture is classified correctly.
6. Orphaned companion overlays fail closed.
7. Supersession claims without transition law fail closed.
8. Planning/support documents cannot emit lock-level authority.
9. Generated projections cannot claim source authority.
10. No `D@1` modal, assertion, selector, predicate, fact, result, or ledger semantics are changed.
```

That would make the implementation family lock-ready.

---

## Recommendation for the next lock

The next lock should select **only `V66-A`** and should explicitly say:

```text
This lock selects repo-scale ANM source discovery and document-class policy only.

It does not select:
- generated reader views
- semantic diff reports
- full migration binding profiles
- prose-boundary notices
- selector-resolution widening
- predicate-contract widening
- new D@1 language forms
- repo-wide Markdown migration
```

The lock should commit the three schema surfaces, package locations, fixture minimums, and fail-closed rules. It should not try to implement the whole `V66` family at once.

---

## Bottom line

These docs are a strong implementation-family setup. They preserve the earlier architecture: ANM-native by authority layer, not repo-wide `.adeu.md` conversion; explicit source posture; no prose laundering; current Markdown authority remains controlling until transition law; `V47` remains closed.

The main fix is to make the family more mechanically precise before locking:

1. split classification axes;
2. define minimal `V66-A` artifact fields;
3. clarify companion checks without full migration profiles;
4. define governed source-set scope;
5. add class-policy matrix and acceptance gates.

After those edits, the bundle is suitable to feed a tight `V66-A` starter lock.
