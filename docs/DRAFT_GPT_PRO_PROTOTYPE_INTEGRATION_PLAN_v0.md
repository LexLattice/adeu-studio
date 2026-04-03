# Draft GPT Pro Prototype Integration Plan v0

Status: planning/support note for maintainer-side intake of four imported prototype
bundles added on April 3, 2026.

Authority layer: planning/support only.

This note does not authorize direct merge of the imported overlays into live repo
surfaces. It records the work needed to translate the prototype bundles into the repo's
internal ADEU methodology.

For the concrete module homes, slice order, and verification plan, see
[docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_GPT_PRO_PROTOTYPE_MODULEIZATION_PLAN_v0.md).

## Intake Baseline

Four imported prototype packs have been normalized under:

- [examples/external_prototypes/adeu-paper-semantic-workbench-poc](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc)
- [examples/external_prototypes/odeu-sandbox-app](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app)
- [examples/external_prototypes/adeu-semantic-forms-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle)
- [examples/external_prototypes/adeu-symbol-audit-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle)

All four should currently be read through
[docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md):

- contribution class: `X2`
- source lane: external single-PR / imported prototype
- precedent status: `non_precedent`
- accepted shipped scope today: intake packs only

## What Was Aligned Now

- the root-level zip payloads were unpacked into repo-owned intake folders rather than
  into live app/package paths
- the accompanying narrative text was preserved as `CLAIMED_SCOPE.md`
- cache artifacts from the sandbox zip were removed
- each pack now has an explicit maintainer alignment note separating:
  - `claimed_scope`
  - `observed_reachable_surfaces`
  - `accepted_shipped_scope`

## Integration Principle

None of these prototypes should be imported directly into live repo paths as a single
diff.

The required move is:

1. preserve the imported prototype as evidence of concept and claimed scope
2. choose the truthful internal family or families
3. slice the work into bounded repo-native arcs
4. re-author the implementation from repo-owned contracts, tests, and docs

The current strongest working thesis is:

- `adeu_semantic_forms` is probably the substrate move
- the other prototype modules should be judged partly by whether they consume that
  substrate or stay intentionally independent

## Prototype A: Paper Semantic Workbench

### Truthful Current Status

- strong concept bundle and UI/workflow overlay
- not a repo-accepted route
- not a repo-accepted schema family
- not a repo-accepted URM template expansion

### Needed Before Full Integration

1. Family decision
   Decide whether this is primarily:
   - a paper-domain artifact family
   - a semantic-analysis workbench family
   - a bounded web visualization family over existing paper artifacts
   - or a mixed family that must be split

2. Scope decomposition
   Separate at least four concerns:
   - source-anchored semantic artifact schema
   - worker request/response contract
   - frontend route and UX behavior
   - harness / workflow template binding

3. Authority discipline
   Freeze:
   - whether the returned structure is advisory-only
   - what remains authoritative in the source artifact
   - what the worker may infer versus what it may claim as explicit
   - how diagnostics are typed and consumed

4. Package ownership normalization
   Decide whether schema should live in `adeu_core_ir`, another package, or a narrower
   package family dedicated to paper semantics.

5. Repo-native implementation path
   Rebuild the chosen first slice from live repo code, not by copying the overlay.

6. Verification
   Add:
   - frontend route tests
   - schema/export checks
   - harness/API tests
   - truthful build/test commands in repo CI

### Recommended First Internal Slice

The safest first internal slice is schema-first and support-first:

- one typed paper semantic artifact candidate
- one bounded worker request contract candidate
- no live route yet
- no live workflow registration yet

That keeps the semantic contract inspectable before product wiring widens.

There is also a separate demonstrator posture worth keeping distinct from the full
internalization order:

- if the repo wants to prove the syntax-of-concepts direction early on a real domain,
  a schema-only paper-semantic contract slice can be pulled earlier
- the full workbench route, worker bridge, and broader product surfaces should still
  remain later

## Prototype C: ADEU Semantic Forms v0

### Truthful Current Status

- strong read-only infra prototype
- close to the released `V45` / `V47` / `V48-A` seam
- still only an imported bundle, not a repo-owned family
- best read, at this stage, as a candidate substrate family for canonical semantic
  language / syntax-of-concepts rather than only as a narrow helper near `V48`

### Needed Before Full Integration

1. Family decision
   Decide whether this is:
   - a new semantic-intent family
   - an extension to an existing semantic-source family
   - or a narrower helper family adjacent to `V48`

2. Authority split
   Freeze the distinction between:
   - fallible `NL -> ADEU` semantic recovery
   - deterministic `ADEU -> ADEU` transform
   - canonical semantic identity / equivalence
   - ambiguity posture

3. Artifact ownership
   Decide which package owns:
   - parse profile
   - semantic normal form
   - transform contract
   - target seed artifact

4. Verification
   Replace sample-only proof with repo-native tests covering:
   - ambiguity posture
   - unsupported rejection
   - canonicalization identity
   - deterministic transform output

### Recommended First Internal Slice

This is a good candidate for the first internalization among the four imports.

Safest first slice:

- one parse-profile artifact
- one semantic normal form artifact
- one transform into a narrow `V48`-adjacent seed
- no broad natural-language language ambition beyond the starter domain

The next truthful move after that should be `A2`, so the repo first accepts the
semantic substrate before choosing broader consumers.

## Prototype D: ADEU Symbol Audit v0

### Truthful Current Status

- strong read-only audit prototype
- parser-first and closure-first
- still only an imported bundle, not a repo-owned package or gate

### Needed Before Full Integration

1. Family decision
   Decide whether this belongs as:
   - a new audit/analysis family
   - a bounded extension near repo-description surfaces
   - or a support-only example lane

2. Authority split
   Freeze the authoritative posture of:
   - symbol census
   - semantic audit
   - coverage report

3. Overlap discipline
   Define how it relates to `repo_symbol_catalog@1` so the repo does not end up with
   two drifting symbol universes.

4. Cross-module semantic decision gate
   Before shipping the semantic audit lane, decide whether the module:
   - reuses `adeu_semantic_forms` primitives
   - or is intentionally independent

5. Verification
   Add repo-native tests for:
   - census determinism
   - local function capture
   - full coverage closure
   - fail-closed incomplete audit handling

### Recommended First Internal Slice

This is the second-best internalization candidate after semantic forms.

Safest first slice:

- census-only and coverage-only
- one frozen pilot slice
- no CLI surface yet
- semantic audit layer only after the census/closure law is accepted

## Prototype B: ODEU Sandbox App

### Truthful Current Status

- strong exploratory simulation package
- self-contained enough to run as a local prototype
- not integrated into repo build, packaging, or ADEU family structure

### Needed Before Full Integration

1. Placement decision
   Decide whether this belongs as:
   - an example pack only
   - a simulation kernel package under `packages/`
   - a web/API app under `apps/`
   - or a split package-plus-app architecture

2. Semantic hardening
   Convert the current concept-rich but still somewhat prose-soft design into:
   - typed ontology surfaces
   - typed lane-crossing contracts
   - typed diagnostics
   - typed scenario and metrics surfaces

3. Scope decomposition
   Split the prototype into:
   - sim kernel
   - API surface
   - UI surface
   - fixture/scenario packs

4. Build normalization
   Replace standalone run guidance with repo-native execution paths using `.venv`,
   `make`, and declared test/lint commands.

5. Verification
   Decide what counts as:
   - deterministic simulation tests
   - API tests
   - UI reachability tests
   - example-pack regression snapshots

### Recommended First Internal Slice

The safest first internal slice is kernel-only:

- one bounded simulation kernel package
- no web surface yet
- no live app integration yet
- one or two frozen scenario fixtures
- typed metrics and regime outputs

That prevents the repo from accepting a whole app before the simulation contract is
typed.

## Cross-Prototype Build Methodology Plan

To fully integrate either prototype into repo methodology, the following sequence is
needed:

1. Intake classification
   Keep the imported packs as evidence and do not erase the original claimed scope.

2. Internal family selection
   Decide whether the work belongs in an existing family or needs a new planning branch.

3. Starter-bundle discipline
   Draft the internal planning and lock docs before product-surface implementation.

4. Package/app placement
   Place code under repo-owned package and app boundaries rather than imported overlay
   paths.

5. Verification wiring
   Add repo-native lint/test commands and CI coverage proportional to the actual shipped
   surface.

6. Closeout discipline
   If adopted as internal ADEU work, finish with the normal assessment/closeout cycle.

## Recommended Immediate Next Move

Do not merge either prototype into live runtime surfaces yet.

Recommended next maintainer action:

- start with `adeu-semantic-forms-v0-bundle`
- open one bounded planning note or arc starter for `A1`
- if `A1` lands cleanly, follow with `A2`
- after `A2`, choose between:
  - `adeu-symbol-audit-v0-bundle` `B1`
  - `adeu-paper-semantic-workbench-poc` `D1` as an earlier schema-only demonstrator
- keep `odeu_sandbox_app` and the broader workbench route deferred until the semantic
  substrate direction is either accepted or intentionally not selected
