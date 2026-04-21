## A. Direct verdict

The optimal end-state is **hybrid ANM-native practice by authority layer**, not a repo-wide rename to `.adeu.md`.

The repo should move toward this steady state:

| Document kind                         | End-state source practice                                                                                                                         | Reason                                                                                                                                                |
| ------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Lock docs**                         | New living locks become **full `.adeu.md`** once transition law is in place. Existing `.md` locks remain controlling until explicitly superseded. | Locks carry implementation authority and should have dense, replayable, compiler-visible semantics.                                                   |
| **Architecture / decomposition docs** | Mostly `.adeu.md` for living architecture, but with sparse authority zones. Legacy architecture docs may use companions first.                    | Architecture needs typed seams, boundaries, decomposition maps, and future-promotion metadata, but should not accidentally become implementation law. |
| **Planning docs**                     | Mixed mode: selected active planning docs become `.adeu.md`; many remain `.md`; companions are common.                                            | Planning needs structured scope guards and candidate-family posture, but weaker normative force than locks.                                           |
| **Support docs**                      | Mostly plain `.md`; optional `.adeu.md` companions or full `.adeu.md` only for reusable governance-support methods.                               | Support docs should remain lightweight and process-oriented unless they contain explicit review discipline worth compiling.                           |
| **Historical docs**                   | Usually remain `.md`, frozen or archived, optionally accompanied by non-overriding ANM overlays.                                                  | Historical authority must not be silently rewritten.                                                                                                  |

So the native practice should be:

> **ANM-first for living governance-bearing docs, companion ANM for migration, plain Markdown for non-governance and historical prose.**

This preserves the current lineage: `D@1` remains a bounded, explicit normative dialect; prose remains prose; compiled semantics come only from recognized authority zones; current Markdown authority is not displaced without explicit transition law.

The existing V47-A through V47-F lineage should be treated as the frozen bootstrap substrate, not replaced:

```text
.adeu.md / companion markdown
  -> D@1 block extraction
  -> typed D-AST
  -> d1_normalized_ir@1
  -> predicate_contracts_bootstrap@1
  -> checker_fact_bundle@1
  -> policy_evaluation_result_set@1
  -> policy_obligation_ledger@1
  -> coexistence / ownership / consumer binding profiles
```

The next-generation design should extend that substrate into repo-scale practice, not invent a new generic Markdown DSL.

---

## B. Full architecture

### B1. Source model

ANM source should have three planes:

```text
1. Prose plane
   Ordinary Markdown.
   Human explanation, rationale, examples, caveats, tradeoffs.
   Never compiled into obligations.

2. Authority-zone plane
   Explicit compiler-recognized blocks only.
   D@1 for normative clauses.
   Future typed blocks for document profile, planning boundary, architecture seams,
   migration bindings, selector ownership, and generated-view manifests.

3. Derived deterministic plane
   Normalized IR, fact bundles, result sets, ledgers, profiles, reader views,
   schema mirrors, and compile reports.
```

The source file may be either:

```text
docs/foo.adeu.md
```

for a standalone ANM document, or:

```text
docs/foo.md
docs/overlays/foo.anm.adeu.md
```

for companion mode during migration.

The existing implementation already supports standalone `.adeu.md` and companion ANM posture. The next step should standardize companion naming and registry behavior so companion files cannot pretend to supersede their hosts.

### B2. Source file anatomy

A canonical `.adeu.md` file should look like this:

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.lock.vnext_plus200"
doc_class: "lock"
authority_layer: "lock"
source_posture: "standalone_anm"
---

# Human title

Human-readable explanation remains normal Markdown.

:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.lock.vnext_plus200
doc_class: lock
authority_layer: lock
allowed_authority_blocks:
  - D@1
current_markdown_authority_relation: standalone_source_of_truth
generated_reader_view: docs/generated/anm/adeu.lock.vnext_plus200.reader.md
:::

More prose.

:::D@1 id=release_surface
ON artifact.emitted[*]
NOTE "Only this D@1 block is compiled as normative source."
@identity MUST REQUIRED snapshot.identity
@identity_explicit MUST EXPLICIT snapshot.identity
@no_scheduler_auth MUST_NOT runtime.scheduler_authority_minted == true
:::
```

Important distinction:

* YAML front matter is useful for editing, indexing, and display.
* It must not by itself mint obligations.
* Normative semantics come only from recognized authority blocks.
* The compiler may validate front matter against the document profile, but it must not lower arbitrary prose or arbitrary metadata into obligations.

### B3. Authority model

ANM must preserve the repo’s existing authority-layer doctrine:

```text
lock
  Direct implementation / release / runtime / artifact authority.

architecture / decomposition
  Conceptual structure, family decomposition, design intent,
  future seams, interpretive boundaries.

planning
  Current planning posture, candidate-family selection, scope guards,
  absence-of-authorization statements.

support
  Review method, process discipline, posture hygiene, result-shape expectations.
```

The same `D@1` clause syntax can appear in multiple document classes, but its **authority layer is not the same**.

A `MUST` in a lock document can become implementation-blocking policy.

A `MUST` in a planning document can express a planning-scope guard, such as “this plan must not be treated as implementation authorization,” but it does not become a lock-level implementation requirement unless promoted by a lock.

A `MUST` in a support document can describe review discipline, but it cannot authorize runtime behavior or release constraints.

Therefore every compiled clause needs a surrounding authority profile:

```text
clause_ref
clause_semantic_hash
source_doc_ref
doc_id
doc_class
authority_layer
source_posture
current_authority_relation
promotion_status
allowed_consumer_worlds
```

The current implementation already has coexistence, ownership, and consumer-binding profiles. The repo-scale design should add a first-class:

```text
anm_doc_authority_profile@1
```

This profile should be generated for every `.adeu.md` source and every companion overlay.

### B4. Deterministic compiler model

The deterministic compiler should become a repo-scale orchestrator built on the existing components.

Recommended pipeline:

```text
1. Discover source set
   - .adeu.md files
   - registered companion overlays
   - legacy .md files with embedded D@1 only where allowed
   - migration registry

2. Classify document authority
   - lock
   - architecture
   - planning
   - support
   - historical
   - non-governance

3. Extract authority blocks
   - exact D@1 block extraction
   - exact future typed block extraction
   - no inference from prose
   - span-aware diagnostics

4. Parse to typed source AST
   - D@1 typed clause AST
   - doc profile AST
   - migration binding AST
   - planning boundary AST
   - architecture seam AST

5. Lower D@1 to normalized D-IR
   - preserve existing d1_normalized_ir@1
   - keep source trace non-semantic
   - produce stable semantic hashes

6. Resolve authority context
   - source posture
   - document class
   - companion relation
   - current Markdown relation
   - promotion/supersession status

7. Resolve selectors and predicate contracts
   - bootstrap selectors allowed initially
   - later O-owned selector handles
   - bootstrap D predicate contracts initially
   - later E-owned predicate contracts

8. Build checker dispatch plan
   - fact-only checkers
   - no verdicts inside checker output
   - no waiver/deferral authority in checkers

9. Emit checker fact bundles
   - checker_fact_bundle@1
   - subject refs
   - path observations
   - explicit carriage observations
   - cardinality observations
   - provenance

10. Evaluate policy
   - policy_evaluation_result_set@1
   - applicability
   - observed outcome
   - effective verdict
   - unknown evidence vs unknown resolution split

11. Project ledger
   - policy_obligation_ledger@1
   - only for authority layers allowed to produce ledgers
   - no fabricated waiver, deferral, approval, or execution authority

12. Emit generated artifacts and views
   - normalized IR
   - result sets
   - ledgers
   - coexistence profiles
   - ownership profiles
   - consumer-binding profiles
   - semantic diff reports
   - reader views
   - compile reports
```

### B5. Deterministic components that remain central

These should stay central and relatively frozen:

1. `D@1` block extraction.
2. `D@1` typed clause model.
3. `d1_normalized_ir@1`.
4. Bootstrap predicate contracts.
5. Fact-only checker bundles.
6. Evaluation result sets.
7. Obligation ledger.
8. Coexistence profile.
9. Selector/predicate ownership profile.
10. Policy and benchmark consumer-binding profiles.
11. Schema export parity between packages and `spec/`.
12. Golden fixtures and fail-closed tests.

These are the core anti-laundering substrate.

### B6. New deterministic components needed for repo-scale adoption

The existing V47-A slice is enough to prove the reference chain. It is not enough to make ANM the daily documentation substrate.

Add these components:

| Component                          | Purpose                                                                                                                             |
| ---------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `anm_source_set_manifest@1`        | Enumerates all ANM sources, companions, hosts, generated views, and active/historical status.                                       |
| `anm_doc_authority_profile@1`      | Declares doc class, authority layer, source posture, allowed block kinds, allowed consumers, and supersession status.               |
| `anm_doc_class_policy@1`           | Machine-checkable rule table saying what each doc class may emit and which failures are hard gates.                                 |
| `anm_migration_binding_profile@1`  | Generalizes coexistence into explicit host/overlay transition law.                                                                  |
| `anm_reader_projection_manifest@1` | Records generated reader views, source hashes, semantic hashes, and drift status.                                                   |
| `anm_semantic_diff_report@1`       | Shows clause additions, removals, semantic-hash changes, authority-layer changes, selector changes, and predicate-contract changes. |
| `anm_prose_boundary_notice_set@1`  | Lint-only notices for prose that appears normative but is not compiled.                                                             |
| `anm_selector_resolution_bundle@1` | Separates selector expansion from checker facts so selector resolution errors are not confused with evidence errors.                |
| `anm_compile_report@1`             | One repo-scale report summarizing diagnostics, hard failures, warnings, generated artifacts, and source set.                        |

These should live in `adeu_commitments_ir` as models and schemas, while `adeu_semantic_compiler` orchestrates them.

### B7. What remains writer-owned and non-deterministic

The following should remain outside deterministic governance:

* narrative explanation
* rationale
* examples
* caveats
* design alternatives
* “why this matters” sections
* future speculation unless captured in explicit seam/promotion structures
* reviewer commentary
* non-authoritative summaries
* generated reader prose that is not marked authoritative

LLMs may assist authors by proposing blocks, but an LLM suggestion has no authority until a human commits explicit ANM authority blocks and the deterministic compiler accepts them.

---

## C. Documentation-class policy

### C1. Lock docs

Lock docs are the highest-value target for ANM.

Policy:

| Question                       | Lock-doc answer                                                                                                                                                 |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Should they become `.adeu.md`? | Yes for new living locks after transition. Existing `.md` locks stay controlling until explicitly superseded.                                                   |
| Companion allowed?             | Yes during migration. Companion overlays must be non-overriding unless a later lock says otherwise.                                                             |
| Density of authority zones     | High. Locks should have the densest `D@1` coverage.                                                                                                             |
| Mandatory blocks               | `anm_doc_authority_profile@1`, lock contract block, `D@1` normative clauses where machine-visible governance matters.                                           |
| Generated artifacts            | D-IR, predicate contracts, fact bundles when evaluated, result sets, obligation ledgers, semantic diff, reader projection manifest.                             |
| CI posture                     | Hard fail on malformed authority zones, unknown selectors, unresolved predicate contracts, schema drift, generated-view drift, prohibited authority laundering. |
| Reader view                    | Recommended, but raw `.adeu.md` remains source.                                                                                                                 |

Lock docs should not formalize every sentence. They should formalize the parts that govern implementation, release, schema, prohibition, acceptance gates, and authority boundaries.

### C2. Architecture / decomposition docs

Architecture docs should use ANM, but not as lock substitutes.

Policy:

| Question                       | Architecture-doc answer                                                                                                                |
| ------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------- |
| Should they become `.adeu.md`? | Living architecture docs should gradually become `.adeu.md`. Older architecture docs may remain `.md` or use companions.               |
| Companion allowed?             | Yes, especially for current architecture notes that should not be rewritten immediately.                                               |
| Density of authority zones     | Medium to sparse.                                                                                                                      |
| Mandatory blocks               | `anm_doc_authority_profile@1`; later `anm_architecture_map@1` or `anm_seam_map@1` for decomposition and future seams.                  |
| `D@1` use                      | For explicit interpretive boundaries, decomposition invariants, and anti-overpromotion rules.                                          |
| Generated artifacts            | Architecture profile, seam map, optional D-IR for explicit D blocks, generated reader view.                                            |
| CI posture                     | Hard fail on malformed blocks; hard fail if architecture doc tries to emit lock-level implementation authority without lock promotion. |
| Ledger                         | No obligation ledger by default. Ledger only if a lock binds the architecture doc into a lock-level obligation surface.                |

Architecture docs should be able to say:

```text
This seam is deferred.
This decomposition is conceptual.
This boundary prevents interpreting X as Y.
This artifact family is not selected yet.
```

They should not silently say:

```text
Implement this now.
Release this schema now.
Treat this as runtime authority.
```

unless a lock binds that intent.

### C3. Planning docs

Planning docs should become partially structured, not fully formal.

Policy:

| Question                                  | Planning-doc answer                                                                                                                                          |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Should they become `.adeu.md`?            | Selected active planning docs should. Many planning docs can remain `.md`.                                                                                   |
| Companion allowed?                        | Yes. Companion mode is ideal for active docs on `main` that already carry planning meaning.                                                                  |
| Density of authority zones                | Low to medium.                                                                                                                                               |
| Mandatory blocks for active planning docs | `anm_doc_authority_profile@1`, `anm_planning_boundary@1`, candidate-family status block, scope guard block.                                                  |
| `D@1` use                                 | Scope guards, absence-of-authorization, current planning boundary, promotion prerequisites.                                                                  |
| Generated artifacts                       | Planning profile, candidate-family map, optional D-IR, semantic diff.                                                                                        |
| CI posture                                | Hard fail for malformed authority blocks; hard fail for overpromotion; softer warning for unstructured prose in low-risk planning docs.                      |
| Ledger                                    | No implementation obligation ledger by default. Planning result sets may exist, but they must not become implementation obligations unless promoted by lock. |

Planning docs should support statements like:

```text
This option is under consideration.
This family is recommended but not yet locked.
This planning doc does not authorize runtime behavior.
This seam requires explicit future promotion.
```

That is exactly where structured ANM helps without making planning painful.

### C4. Support docs

Support docs should mostly stay Markdown.

Policy:

| Question                       | Support-doc answer                                                                                                   |
| ------------------------------ | -------------------------------------------------------------------------------------------------------------------- |
| Should they become `.adeu.md`? | Usually no. Use `.adeu.md` only when the support doc contains reusable process discipline or testable posture rules. |
| Companion allowed?             | Yes, but sparse.                                                                                                     |
| Density of authority zones     | Low.                                                                                                                 |
| Mandatory blocks               | None for ordinary support docs. `anm_doc_authority_profile@1` if the support doc becomes ANM-aware.                  |
| `D@1` use                      | Rare. Only support-layer obligations such as review-shape discipline or artifact hygiene.                            |
| Generated artifacts            | Usually none. Optional support profile or reader view.                                                               |
| CI posture                     | Validate authority blocks if present. Prevent support docs from emitting lock/planning authority.                    |
| Ledger                         | No lock ledger. Support-layer checklists may produce lint reports, not implementation obligations.                   |

Support docs should remain useful to humans. ANM should not turn them into bureaucratic syntax.

---

## D. Migration strategy

The migration must not be “rename everything.”

The repo should move through staged coexistence.

### Stage 0 — Inventory and classification

Create a source-set inventory:

```text
docs/ANM_SOURCE_SET_MANIFEST.adeu.md
```

or generated artifact:

```text
artifacts/anm/source_set_manifest.json
```

Classify each document as:

```text
lock
architecture
planning
support
historical
non_governance
generated
unknown
```

Also classify:

```text
living
historical
superseded
generated_view
companion_overlay
source_of_truth
```

The initial inventory should record that existing `.md` docs remain source-of-truth unless individually transitioned.

### Stage 1 — Coexistence without supersession

Use companion overlays for important existing docs.

Example:

```text
docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md
docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS106.anm.adeu.md
```

The companion overlay may compile explicit clauses, but the overlay must declare:

```text
current_markdown_authority_relation: current_markdown_controlling
companion_authority_relation: coexisting_non_override
requires_later_lock_for_supersession: true
```

This matches the existing coexistence doctrine in the V47-C fixtures: current Markdown is not silently overridden, and later lock authority is required for supersession.

### Stage 2 — New greenfield ANM for new locks

New lock documents should be written directly as `.adeu.md`.

Example:

```text
docs/LOCKED_CONTINUATION_vNEXT_PLUS200.adeu.md
```

For a transition period, generated reader views may be emitted:

```text
docs/generated/anm/LOCKED_CONTINUATION_vNEXT_PLUS200.reader.md
```

The reader view is non-authoritative unless an explicit lock says otherwise.

### Stage 3 — Active planning docs get structured boundaries

Active planning docs such as next-arc options, stop-gate decisions, and assessments should gain ANM boundaries first, not full normative density.

Use:

```text
anm_planning_boundary@1
anm_candidate_family_status@1
anm_scope_guard@1
```

These blocks should answer:

```text
What does this planning doc authorize?
What does it not authorize?
Which family is selected, recommended, deferred, or not selected?
Which future seams remain live?
Which promotion rule would be needed to make this implementation-authoritative?
```

### Stage 4 — Architecture seam maps

Living architecture docs should gradually gain structured decomposition and future-seam maps.

Use:

```text
anm_architecture_map@1
anm_future_seam_map@1
anm_promotion_surface@1
```

This directly builds on the current authority-layering note, intent-horizon glossary, and future-seam promotion rules.

### Stage 5 — Explicit supersession law for selected legacy docs

A legacy `.md` doc may stop being source-of-truth only when a lock-level transition block says so.

The transition law must identify:

```text
legacy_source_doc_ref
new_anm_source_doc_ref
supersession_scope
effective_commit_or_release
preserved_historical_status
generated_reader_view_policy
known_non-equivalences
migration_reviewer
```

No implicit supersession by filename, location, or generated artifact is allowed.

### Stage 6 — ANM-native default for new governance docs

Once the tooling is reliable:

* new lock docs default to `.adeu.md`
* new living architecture docs default to `.adeu.md`
* active planning docs use `.adeu.md` or registered companions
* support docs remain `.md` unless they need structured support semantics
* historical docs remain as they are

This gets the repo to ANM-native practice without breaking governance clarity.

---

## E. Implementation roadmap

### Slice 1 — Repo-scale source discovery and class policy

Goal: make the compiler understand the repo, not just individual fixtures.

Implement:

```text
anm_source_set_manifest@1
anm_doc_authority_profile@1
anm_doc_class_policy@1
```

Add CLI entrypoints:

```bash
make anm-inventory
make anm-check
make anm-compile
make anm-diff
```

Minimum checks:

* detect `.adeu.md`
* detect registered companions
* detect embedded `D@1`
* reject unregistered companions
* reject companion supersession claims without lock
* classify document authority
* report unknown/unclassified governance docs

This slice should not widen `D@1`.

### Slice 2 — Better parser diagnostics and authoring lint

Goal: make humans able to write ANM without hating it.

Extend `adeu_semantic_source`:

* span-aware diagnostics
* stable error codes
* block ID uniqueness across source set
* clause label uniqueness per block
* exact source location in compile report
* `NOTE` treated as non-semantic
* prose-normative-word notices
* no-prose-laundering diagnostics

Add an ANM formatter with conservative behavior:

* normalize `D@1` indentation
* preserve prose
* preserve clause order
* do not rewrite human sections
* optionally align labels and modals

### Slice 3 — Generated reader views and semantic diffs

Goal: make review and reading pleasant.

Implement:

```text
anm_reader_projection_manifest@1
anm_semantic_diff_report@1
```

Generated reader views should:

* preserve prose
* render `D@1` blocks as readable tables
* show authority layer
* show whether the document is standalone or companion
* show whether the reader view is generated and non-authoritative
* include source and semantic hashes

Semantic diff should show:

```text
added clauses
removed clauses
changed clause semantic hashes
changed selectors
changed predicate refs
changed authority layer
changed source posture
changed generated artifacts
```

Code review should not require reviewers to mentally diff normalized JSON.

### Slice 4 — Migration registry and coexistence hardening

Goal: prevent silent drift during the mixed `.md` / `.adeu.md` era.

Generalize the existing coexistence profile into repo-scale migration law.

Implement checks for:

* orphaned overlays
* stale host hashes
* companion refers to missing host
* host changed without overlay acknowledgement
* overlay tries to supersede host
* generated reader view out of date
* doc class mismatch
* support/planning overpromotion

### Slice 5 — Selector and predicate ownership transition

Goal: move beyond bootstrap without breaking V47-A.

Keep bootstrap selectors/predicates valid, but introduce registries:

```text
O-owned selector registry
E-owned predicate contract registry
selector/predicate compatibility matrix
```

Preserve the existing V47-D ownership posture:

* bootstrap remains allowed
* imported O selectors require explicit resolution
* imported E predicates require explicit contract compatibility
* unsupported combinations fail closed
* no checker may smuggle predicate meaning

### Slice 6 — Class-specific typed blocks

Goal: widen the authoring model without bloating `D@1`.

Add typed blocks outside `D@1`:

```text
:::adeu.planning_boundary@1
...
:::

:::adeu.architecture_map@1
...
:::

:::adeu.future_seam_map@1
...
:::

:::adeu.migration_binding@1
...
:::

:::adeu.reader_projection@1
...
:::
```

These are not freeform. They have schemas.

This avoids forcing everything through `D@1` while still keeping governance-relevant metadata explicit and replayable.

### Slice 7 — Limited semantic widening of `D@1`

Only after the above is stable, widen `D@1`.

Candidate order:

1. `AT_LEAST` / `AT_MOST` cardinality constructors.
2. Better list equality if canonical evidence supports it.
3. `SHOULD` as warning-level advisory semantics, not blocking obligations.
4. `MAY` as explicit permission semantics, not obligation.
5. `BEFORE` / `AFTER` only once event/timestamp evidence is well-typed.
6. Bounded conjunction only if the evaluator and diagnostics remain simple.

Do not add general boolean algebra, quantifiers, theorem proving, or prose inference as an early step.

---

## F. Repo-shape recommendations

### F1. Package ownership

Keep the current package split, but clarify responsibilities.

```text
packages/adeu_semantic_source/
  ANM source extraction, D@1 parser, typed source AST,
  source diagnostics, source posture inference.

packages/adeu_commitments_ir/
  Pydantic models, schema export, normalized IR models,
  fact bundle models, result set models, ledger models,
  doc profile models, migration profile models.

packages/adeu_semantic_compiler/
  Repo-scale orchestration, source discovery, pass pipeline,
  artifact emission, semantic diff, generated views,
  CI-facing commands.

packages/adeu_semantic_tools/          # optional later
  Formatting, snippets, editor metadata, authoring helpers.
```

Do not move the V47-A code out of `adeu_semantic_source` prematurely. First wrap it from `adeu_semantic_compiler`.

### F2. Schema locations

Use package-owned schemas as authoritative and mirror them to `spec/`.

Recommended:

```text
packages/adeu_commitments_ir/schema/
  d1_normalized_ir.schema.json
  predicate_contracts_bootstrap.schema.json
  checker_fact_bundle.schema.json
  policy_evaluation_result_set.schema.json
  policy_obligation_ledger.schema.json
  anm_doc_authority_profile.schema.json
  anm_source_set_manifest.schema.json
  anm_doc_class_policy.schema.json
  anm_migration_binding_profile.schema.json
  anm_reader_projection_manifest.schema.json
  anm_semantic_diff_report.schema.json

spec/anm/
  mirrored schemas
  schema export report
```

CI should fail if package schema export and `spec/` mirrors drift.

### F3. Source locations

Recommended conventions:

```text
docs/*.adeu.md
  First-class standalone ANM docs.

docs/overlays/*.anm.adeu.md
  Companion overlays for existing .md docs.

docs/generated/anm/
  Human reader views. Non-authoritative by default.

docs/anm/
  Authoring guide, document-class policy, migration registry,
  templates, examples.

artifacts/anm/<snapshot-or-arc>/
  Machine outputs from ANM compilation.
```

For active locks:

```text
docs/LOCKED_CONTINUATION_vNEXT_PLUS200.adeu.md
artifacts/anm/vNEXT_PLUS200/d1_normalized_ir.json
artifacts/anm/vNEXT_PLUS200/policy_evaluation_result_set.json
artifacts/anm/vNEXT_PLUS200/policy_obligation_ledger.json
docs/generated/anm/LOCKED_CONTINUATION_vNEXT_PLUS200.reader.md
```

For companions:

```text
docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md
docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS106.anm.adeu.md
artifacts/anm/vNEXT_PLUS106/coexistence_profile.json
```

### F4. CI hooks

Minimum CI gates:

```text
anm:inventory
  source set is valid

anm:parse
  all registered ANM parses fail-closed

anm:schema
  model/schema export parity

anm:compile
  deterministic compile succeeds

anm:fixtures
  V47-A through V47-F fixtures replay

anm:class-policy
  no doc overpromotes its authority layer

anm:migration
  no companion supersedes legacy markdown without transition law

anm:views
  generated reader views are current, if committed

anm:diff
  semantic diff is present for authority-bearing changes
```

Recommended local commands:

```bash
make anm-check
make anm-compile
make anm-diff
make anm-format
make anm-view
```

### F5. Maintainer workflow

A normal maintainer flow should be:

```text
1. Edit prose and explicit authority blocks in .adeu.md.
2. Run make anm-check.
3. Review semantic diff.
4. Update generated reader view only if the repo commits generated views.
5. Open PR.
6. Reviewers inspect:
   - human prose
   - D@1 blocks
   - semantic diff
   - generated result/ledger where relevant
   - migration/coexistence profile if companion mode is involved
7. CI enforces deterministic replay.
```

The reviewer should not have to reverse-engineer normalized IR by hand.

---

## G. Example file forms

### G1. Lock-level standalone `.adeu.md`

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.lock.vnext_plus200"
doc_class: "lock"
authority_layer: "lock"
source_posture: "standalone_anm"
---

# LOCKED CONTINUATION vNEXT+200

This document is a lock-level implementation contract.

The prose explains scope, rationale, and reviewer intent. The compiled
obligations come only from explicit authority blocks.

:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.lock.vnext_plus200
doc_class: lock
authority_layer: lock
source_posture: standalone_anm
allowed_authority_blocks:
  - D@1
emits:
  - d1_normalized_ir@1
  - policy_evaluation_result_set@1
  - policy_obligation_ledger@1
supersedes: []
:::

## Scope

This slice implements the bounded ANM repo-native adoption substrate.
It does not authorize scheduler behavior, mutation authority, or prose-derived
policy inference.

:::D@1 id=lock_release_surface
ON artifact.emitted[*]
NOTE "Only explicit D@1 clauses compile into lock-level obligations."
@identity MUST REQUIRED snapshot.identity
@identity_explicit MUST EXPLICIT snapshot.identity
@primary_carrier MUST EXACTLY_ONE primary_carrier_class
@no_prose_laundering MUST_NOT semantic_source.prose_inference_enabled == true
@no_scheduler_auth MUST_NOT runtime.scheduler_authority_minted == true
:::

## Acceptance Gates

The implementation must preserve source, IR, fact, result, and ledger separation.

:::D@1 id=lock_acceptance_gates
ON artifact.emitted[*]
@schema_export MUST REQUIRED schema_export.parity_report
@fact_only_checkers MUST_NOT checker.policy_verdict_emitted == true
@ledger_no_minting MUST_NOT ledger.waiver_authority_minted == true
:::
```

This is the right shape for new lock docs: readable prose plus explicit, bounded authority zones.

### G2. Planning-level `.adeu.md`

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.planning.next_arc_options_v60"
doc_class: "planning"
authority_layer: "planning"
source_posture: "standalone_anm"
---

# Draft Next Arc Options v60

This planning document compares possible next implementation families.
It does not, by itself, authorize implementation.

:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.planning.next_arc_options_v60
doc_class: planning
authority_layer: planning
source_posture: standalone_anm
allowed_authority_blocks:
  - adeu.planning_boundary@1
  - D@1
emits:
  - anm_planning_profile@1
  - anm_semantic_diff_report@1
does_not_emit:
  - policy_obligation_ledger@1
:::

:::adeu.planning_boundary@1
schema: anm_planning_boundary@1
planning_status: candidate_selection
selected_family: anm_repo_native_practice
implementation_authority: false
requires_lock_for_implementation: true
explicit_non_authorizations:
  - runtime_execution
  - scheduler_authority
  - legacy_markdown_supersession
  - repo_wide_rename
:::

## Recommended family

The recommended family is repo-native ANM adoption: source-set inventory,
document-class policy, companion migration, generated reader views, and
class-aware CI gates.

:::D@1 id=planning_scope_guards
ON companion.section[*]
NOTE "Planning-layer guard only. This does not become lock-level implementation authority."
@planning_only MUST section.authority_layer == "planning"
@requires_lock MUST section.implementation_authority == false
@no_supersession MUST_NOT section.supersedes_legacy_markdown == true
:::
```

This lets planning docs be structured and reviewable without pretending they are locks.

### G3. Architecture-level `.adeu.md`

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.architecture.anm_native_substrate_v1"
doc_class: "architecture"
authority_layer: "architecture"
source_posture: "standalone_anm"
---

# Architecture: ANM-Native Documentation Substrate

This architecture describes the conceptual decomposition of the ANM substrate.
It is architecture-authoritative, not implementation-authoritative by itself.

:::adeu.doc_profile@1
schema: anm_doc_authority_profile@1
doc_id: adeu.architecture.anm_native_substrate_v1
doc_class: architecture
authority_layer: architecture
allowed_authority_blocks:
  - adeu.architecture_map@1
  - adeu.future_seam_map@1
  - D@1
requires_lock_for:
  - implementation_scope
  - release_blocking_obligations
  - schema_release
:::

:::adeu.architecture_map@1
schema: anm_architecture_map@1
components:
  - id: source_model
    role: prose_and_authority_zone_carrier
  - id: d1_lowering
    role: normative_clause_lowering
  - id: fact_bundle
    role: evidence_carrier_only
  - id: evaluator
    role: verdict_computation
  - id: ledger
    role: derived_current_state
forbidden_collapses:
  - source_to_fact
  - prose_to_obligation
  - checker_to_verdict
  - ledger_to_waiver_authority
:::

## Boundary invariant

The architecture depends on keeping human prose and compiled obligations separate.

:::D@1 id=architecture_boundary_invariants
ON companion.section[*]
NOTE "Architecture-layer invariant; implementation force requires a binding lock."
@no_prose_policy MUST_NOT section.prose_inference_enabled == true
@fact_only_checker_boundary MUST_NOT section.checker_mints_policy_verdict == true
:::
```

This captures architecture semantics without overpromoting them.

### G4. Support doc with optional companion

Legacy support doc remains:

```text
docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md
```

Optional companion:

```text
docs/overlays/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.anm.adeu.md
```

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.support.anm_d1_arc30_seed_v1_overlay"
doc_class: "support"
authority_layer: "support"
source_posture: "companion_anm"
host_doc_ref: "docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md"
---

# Companion Overlay: ANM D1 ARC30 Source Seed v1

This overlay records support-layer interpretation boundaries.
It does not supersede the host Markdown document.

:::adeu.migration_binding@1
schema: anm_migration_binding_profile@1
host_doc_ref: docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md
overlay_doc_ref: docs/overlays/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.anm.adeu.md
current_markdown_authority_relation: current_markdown_controlling
overlay_authority_relation: coexisting_non_override
requires_later_lock_for_supersession: true
:::

:::D@1 id=support_non_override
ON companion.section[*]
NOTE "Support-layer guard only."
@non_override MUST section.overlay_authority_relation == "coexisting_non_override"
@no_lock_authority MUST_NOT section.claims_lock_authority == true
:::
```

This is the right migration posture for support lineage: useful, explicit, non-overriding.

### G5. Companion migration case for a legacy lock

Existing controlling source:

```text
docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md
```

Companion overlay:

```text
docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS106.anm.adeu.md
```

```markdown
---
anm_format: "ANM@1"
doc_id: "adeu.lock.vnext_plus106.overlay"
doc_class: "lock"
authority_layer: "lock"
source_posture: "companion_anm"
host_doc_ref: "docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md"
---

# ANM Companion Overlay for LOCKED_CONTINUATION vNEXT+106

This file compiles selected explicit lock semantics from the existing lock.
It does not supersede the host Markdown file.

:::adeu.migration_binding@1
schema: anm_migration_binding_profile@1
host_doc_ref: docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md
overlay_doc_ref: docs/overlays/LOCKED_CONTINUATION_vNEXT_PLUS106.anm.adeu.md
current_markdown_authority_relation: current_markdown_controlling
overlay_authority_relation: coexisting_non_override
supersession_status: not_superseded
requires_later_lock_for_supersession: true
allowed_overlay_actions:
  - reference
  - compile_selected_explicit_clauses
  - emit_non_overriding_d_ir
  - emit_migration_signal
forbidden_overlay_actions:
  - replace_host_authority
  - broaden_lock_scope
  - mint_runtime_authority
:::

:::D@1 id=v106_authority_boundaries
ON companion.section[*]
NOTE "Companion overlay; current Markdown lock remains controlling."
@host_controls MUST section.current_markdown_authority_relation == "current_markdown_controlling"
@no_silent_supersession MUST_NOT section.supersedes_host == true
@no_checker_minting MUST_NOT section.checker_authority_minting_enabled == true
@no_ledger_minting MUST_NOT section.ledger_authority_minting_enabled == true
:::
```

This is the pattern that prevents silent authority drift during migration.

---

## H. Robustness and failure posture

### H1. Malformed authority zones

Malformed authority zones fail closed.

| Context                 | Behavior                                                                                                             |
| ----------------------- | -------------------------------------------------------------------------------------------------------------------- |
| Lock `.adeu.md`         | Hard compile failure and CI failure.                                                                                 |
| Architecture `.adeu.md` | Hard failure for that document; CI failure if living architecture.                                                   |
| Planning `.adeu.md`     | Hard failure for active planning docs; warning or quarantine only for inactive drafts, depending on registry status. |
| Support `.adeu.md`      | Hard failure if registered as ANM; ignored if plain `.md` with no registered authority blocks.                       |
| Historical `.md`        | No ANM compilation unless registered.                                                                                |

Unsupported syntax must not degrade into prose interpretation.

### H2. Unresolved selectors

Unresolved selectors produce `unknown_resolution`.

For lock-level docs:

```text
unknown_resolution -> blocking result
```

If no subject can be resolved, the result remains clause-scoped and must not fabricate ledger rows.

This preserves the current D@1 distinction:

```text
unknown_resolution != unknown_evidence
zero_match != unknown_resolution
gated_off != pass
waived != satisfied
```

### H3. Missing evidence

Missing or inconclusive evidence produces `unknown_evidence`.

If the subject is resolved, the ledger may record:

```text
blocked_unknown_evidence
```

The checker does not decide compliance. It only emits facts.

### H4. Prose and authority block disagreement

If prose and `D@1` disagree:

1. The compiler must not infer new policy from prose.
2. The `D@1` block remains the only machine-consumed normative source.
3. A lint notice should flag possible disagreement.
4. For lock docs, CI should require human review or an explicit waiver to merge.
5. No automatic “semantic reconciliation” is allowed.

This is the anti-laundering line.

### H5. Generated view drift

Generated reader views are derived.

If committed generated views drift:

```text
CI fails.
```

But the source remains the `.adeu.md` file or explicitly controlling legacy `.md` host.

Generated views must contain a banner:

```text
Generated reader view.
Non-authoritative unless explicitly bound by a lock.
Source: ...
Source hash: ...
Semantic hash: ...
```

### H6. Companion overlay contradicts legacy host

During migration, the host Markdown remains controlling unless a transition lock says otherwise.

If an overlay contradicts the host or claims supersession without authority:

```text
coexistence validation fails
overlay cannot become source-of-truth
CI blocks if active
```

The overlay may compile selected explicit semantics for analysis, but not rewrite history.

### H7. Planning/support overpromotion

A planning or support document must not emit lock-level obligations.

The class-policy validator should reject:

```text
planning doc -> policy_obligation_ledger@1 as implementation authority
support doc -> runtime consumer binding
architecture doc -> release-blocking obligation without lock binding
companion overlay -> supersession without transition law
```

This is how authority layering stays real rather than decorative.

---

## I. Semantic flexibility without prose laundering

The core design principle is:

> ANM should make machine-governed semantics explicit without making all thought machine-governed.

The boundary should be enforced by four rules.

### Rule 1 — Compiler recognition is syntactic, not interpretive

Only exact authority blocks are recognized.

Recognized now:

```text
:::D@1 id=...
...
:::
```

Recognized later:

```text
:::adeu.doc_profile@1
:::adeu.planning_boundary@1
:::adeu.architecture_map@1
:::adeu.future_seam_map@1
:::adeu.migration_binding@1
```

Everything else is prose.

Words such as “must,” “should,” “forbidden,” and “required” in ordinary prose may trigger lints, but never become obligations.

### Rule 2 — `D@1` remains small and typed

Keep the current V47-A shape:

```text
one modal head
one assertion body
optional qualifiers
no arbitrary boolean algebra
no source-level DEFERRED
no prose inference
```

Current live forms:

```text
MUST
MUST_NOT

REQUIRED path
EXPLICIT path
EXACTLY_ONE path
predicate_call(...)
path == scalar
```

Qualifiers:

```text
ONLY_IF condition
UNLESS condition
```

This is the right tradeoff: enough for stable governance clauses, not enough to become a hidden programming language.

### Rule 3 — Richer document meaning goes into typed side blocks, not arbitrary prose

Planning docs need planning boundaries.

Architecture docs need seam maps.

Migration needs binding profiles.

Reader views need projection manifests.

Do not overload `D@1` with all of that. Add typed blocks with schemas.

### Rule 4 — LLMs can assist but cannot govern

Allowed:

```text
LLM proposes candidate D@1 clauses.
LLM explains a semantic diff.
LLM suggests migration overlays.
LLM drafts reader prose.
```

Not allowed:

```text
LLM infers obligations from prose and feeds them to CI as authority.
LLM decides that prose supersedes a lock.
LLM resolves unknown evidence.
LLM mints waiver, deferral, approval, or runtime authority.
```

The committed source and deterministic compiler remain the authority path.

---

## J. Future semantic widening

### J1. What should stay frozen

Freeze these until the repo has adopted ANM operationally:

```text
no prose-derived obligations
D@1 exact authority-zone requirement
source / IR / fact / result / ledger separation
fact-only checkers
unknown_evidence vs unknown_resolution split
zero-match allow_empty_with_notice semantics
no source-level DEFERRED
no checker authority minting
no ledger authority minting
current Markdown non-override during migration
lock / architecture / planning / support separation
```

Also freeze the existing schema IDs for the bootstrap line:

```text
d1_normalized_ir@1
predicate_contracts_bootstrap@1
checker_fact_bundle@1
policy_evaluation_result_set@1
policy_obligation_ledger@1
```

If semantics change incompatibly, version forward rather than mutating these meanings.

### J2. What should widen first

Widen ergonomics before widening logic.

Order:

1. Better diagnostics.
2. Better source-set inventory.
3. Better generated reader views.
4. Semantic diffs.
5. Migration registry.
6. Class-policy validation.
7. Selector/predicate ownership registries.
8. Planning and architecture typed blocks.
9. Limited new `D@1` constructors.

This makes adoption practical before making the language more powerful.

### J3. What should widen later

Later semantic widening may include:

```text
AT_LEAST path n
AT_MOST path n
SHOULD assertion
MAY assertion
BEFORE condition
AFTER condition
bounded AND only inside condition lists
cross-doc clause references
owned selector handles
owned predicate-contract imports
semantic refactoring tools
```

But each addition needs:

```text
source syntax
AST model
normalized IR representation
predicate or evaluator semantics
fact/evidence requirements
result mapping
ledger mapping, if applicable
fixtures
schema export
migration notes
failure behavior
```

No widening should be accepted merely because it is convenient in prose.

---

## K. Explicit tradeoffs

### What becomes deterministic

The following should be deterministic and compiler-visible:

```text
authority block extraction
D@1 clause parsing
normalized D-IR
selector references
predicate contract references
fact bundle shape
policy evaluation result shape
ledger projection
document authority profiles
migration bindings
class-policy validation
generated reader projection manifests
semantic diffs
schema export parity
```

### What stays flexible

The following stays human-owned:

```text
ordinary Markdown prose
rationale
examples
caveats
discussion
design alternatives
historical narrative
review commentary
non-authoritative generated summaries
```

### What remains prose-only

Some governance-adjacent material should remain prose unless a maintainer intentionally promotes it:

```text
motivation
why a path was chosen
known discomfort
exploratory alternatives
historical context
non-binding recommendations
open questions
```

### Where friction is intentionally introduced

ANM should introduce friction at these points:

| Friction                                            | Why it is worth it                       |
| --------------------------------------------------- | ---------------------------------------- |
| Writing explicit `D@1` clauses for lock obligations | Prevents accidental policy from prose.   |
| Declaring document class and authority layer        | Prevents planning/support overpromotion. |
| Registering companions                              | Prevents silent legacy-doc supersession. |
| Selector/predicate contract checks                  | Prevents hidden checker semantics.       |
| Generated semantic diffs                            | Makes review reliable.                   |
| Schema export parity                                | Keeps compiler and spec aligned.         |
| Hard failure on malformed authority zones           | Keeps governance replayable.             |

This is acceptable friction because it appears where authority matters. Ordinary prose remains easy.

---

## Final design summary

The repo should not become “all formal syntax.” It should become **ANM-native where governance is real**.

The next-generation ADEU ANM substrate should be:

```text
Markdown-first for humans.
Explicit authority zones for governance.
D@1 frozen as the bounded normative kernel.
Typed side blocks for doc profiles, planning boundaries, architecture seams,
migration bindings, and generated views.
Deterministic compiler pipeline from source to IR to facts to results to ledger.
Class-aware authority policy.
Companion-first migration.
Explicit supersession law.
Generated reader views and semantic diffs for daily usability.
No prose laundering. No LLM authority path. No silent Markdown replacement.
```

That is the path from the current V47-A bounded implementation branch to a repo-native documentation practice the project can actually live in.
