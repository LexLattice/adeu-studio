# Draft GPT Pro Prototype Moduleization Plan v0

Status: planning/support note for turning imported GPT Pro prototype bundles into
repo-native ADEU modules.

Authority layer: planning/support only.

This note does not authorize direct implementation by itself. It defines the concrete
module homes, slice order, and verification expectations that would be required if the
imported prototype bundles are internalized through the repo's normal ADEU workflow.

Read together with:

- [docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_GPT_PRO_PROTOTYPE_INTEGRATION_PLAN_v0.md)
- [docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md](/home/rose/work/LexLattice/odeu/docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md)

## Scope

The current imported intake packs are:

- [examples/external_prototypes/adeu-semantic-forms-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle)
- [examples/external_prototypes/adeu-symbol-audit-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle)
- [examples/external_prototypes/odeu-sandbox-app](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app)
- [examples/external_prototypes/adeu-paper-semantic-workbench-poc](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc)

All four remain:

- imported external `X2` bundles
- `non_precedent`
- intake-only today

## Internalization Order

Recommended order:

1. `adeu_semantic_forms`
2. `adeu_symbol_audit`
3. `adeu_odeu_sim`
4. `adeu_paper_semantics` plus the paper semantic workbench route

Reason:

- `adeu_semantic_forms` is closest to already released `V45` / `V47` / `V48` infra
  and is read-only
- `adeu_symbol_audit` is also read-only and closure-oriented, but it must be related
  carefully to `repo_symbol_catalog@1`
- `adeu_odeu_sim` is larger because it introduces a new kernel plus future app/API
  surfaces
- the paper semantic workbench has the widest blast radius because it touches web,
  schema, worker contract, and domain template surfaces together

This order should be read as the safest full-module internalization order, not as a
claim that every schema-first demonstrator must wait for every earlier full module to
finish.

## Cross-Module Internal ADEU Sequence

Every prototype should be converted through the same six-step sequence:

1. **Planning selection**
   Decide whether the module needs a new family or fits an existing family boundary.

2. **Starter bundle**
   Draft the planning/lock artifacts for one bounded first slice.

3. **Package-first implementation**
   Create the repo-owned package/module contract before broader consumers are wired.

4. **Focused verification**
   Add repo-native unit/schema/fixture tests proportional to the slice.

5. **Consumer wiring**
   Only after the package contract is accepted should API/web/CLI surfaces widen.

6. **Closeout**
   Record what was actually shipped and what remained deferred.

## Cross-Module Dependency Table

The current dependency posture between the proposed modules/slices is:

| Slice | Dependency posture | Planning note |
|---|---|---|
| `A1` semantic contracts | independent | highest-priority substrate candidate |
| `A2` semantic recovery | depends on `A1` | first `NL -> ADEU` lane |
| `A3` deterministic lowering | depends on `A1` and `A2` | first `ADEU -> ADEU` lowering lane |
| `A4` downstream bridge | depends on `A3` plus released `V48-A` / `V48-B` | bridge only after the semantic substrate is frozen |
| `B1` symbol census / coverage | independent | may run in parallel with `A2` if desired |
| `B2` semantic audit ledger | soft dependency on `A1` decision | decide whether to reuse Module A semantic primitives or stay intentionally independent |
| `D1` paper semantic contract | soft dependency on `A1` and `A2` | preferred if syntax-of-concepts consistency matters |
| `C1` simulation kernel | independent | strategically lower priority unless simulation becomes the immediate focus |

The most coherent execution order implied by this table is:

1. `A1`
2. `A2`
3. then choose between `B1` and `D1`
4. defer `C1` and the broader workbench until the semantic substrate direction is
   either accepted or intentionally not selected

## Repo-Level Full-Module Alignment Tasks

For any of the four prototypes to count as a full repo module rather than only an
intake pack, the moduleization work has to align not just the code but also the repo's
build and verification methodology.

Every internalized module should therefore add, in order:

1. **Package scaffold**
   Create a repo-owned package with:
   - `packages/<module>/pyproject.toml`
   - `packages/<module>/src/<module>/`
   - `packages/<module>/tests/`

2. **Contract-first ownership**
   Move only the accepted core contracts into the live package.
   Keep the imported intake pack under
   [examples/external_prototypes](/home/rose/work/LexLattice/odeu/examples/external_prototypes)
   as support evidence rather than copying it wholesale.

3. **Repo-native verification**
   Ensure the first accepted slice is reachable by the repo's normal Python lane:
   - `make check` for full PR gating
   - targeted `pytest` lanes during bounded implementation work
   - `ruff` via the repo root configuration in
     [pyproject.toml](/home/rose/work/LexLattice/odeu/pyproject.toml)

4. **Schema/export placement**
   If the module ships committed schemas, place them under:
   - `packages/<module>/schema/`
   - [spec](/home/rose/work/LexLattice/odeu/spec)
   and add deterministic export/regeneration checks before treating them as stable.

5. **Consumer-widening discipline**
   Do not add CLI, API, or web consumers until the underlying package contract is
   accepted and tested.

6. **Example retention**
   Preserve the original imported bundle and any truthful local hot-mode/example packs
   under [examples](/home/rose/work/LexLattice/odeu/examples) even after moduleization,
   so the repo keeps the concept artifact separate from the shipped module contract.

7. **Maintainer closeout**
   Once a slice is accepted, record:
   - claimed scope from the intake pack
   - observed reachable surfaces in the repo diff
   - accepted shipped scope in the closeout note
   so the imported prototype does not accidentally become process precedent.

## Immediate Moduleization Program

The concrete program for the next internalization pass should be:

1. start with `adeu_semantic_forms`
2. treat `Module A / Slice A1` as the first starter-bundle candidate
3. keep `adeu_symbol_audit`, `adeu_odeu_sim`, and `adeu_paper_semantics` intake-only
   until `A1` lands with repo-native tests and closeout
4. only after `A1` proves clean package ownership, verification, and accepted scope,
   draft the next starter for `A2`
5. after `A2`, choose the next bounded consumer lane:
   - `Module B / Slice B1`
   - or `Module D / Slice D1` if an earlier domain demonstrator is more valuable

## Module A: `adeu_semantic_forms`

### Target End State

Target repo home:

- `packages/adeu_semantic_forms/src/adeu_semantic_forms/`
- `packages/adeu_semantic_forms/tests/`
- optional schema export home if needed:
  - `packages/adeu_semantic_forms/schema/`
  - `spec/`

Imported bundle reference:

- [examples/external_prototypes/adeu-semantic-forms-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-semantic-forms-v0-bundle)

### Full Module Goal

Provide a repo-owned substrate family for canonical semantic language / syntax-of-
concepts, with:

- parse profiles over released anchors
- canonical semantic normal forms
- canonical semantic identity and equivalence law
- typed ambiguity / unsupported outcomes
- deterministic transforms into a narrow downstream seed artifact

### Concrete Slice Plan

#### Slice A1: Core contracts

Create:

- `models.py`
- `parse_profile.py`

Freeze:

- parse profile schema
- semantic normal form schema
- parse result schema
- transform contract schema
- canonical semantic identity law
- canonical hash subject
- semantic equivalence posture
- ambiguity posture

Do not include yet:

- generalized natural language
- arbitrary boolean composition
- runtime integration

Required verification:

- model validation tests
- canonical hash stability tests
- sample artifact round-trip tests

#### Slice A2: Recovery engine

Create:

- `parser.py`

Freeze:

- `NL -> ADEU` recovery posture only
- starter domain `repo_policy_work`
- `resolved_singleton`
- `typed_alternatives`
- `clarification_required`
- `rejected_unsupported`

Required verification:

- ambiguity tests
- unsupported-pattern tests
- alias normalization tests
- prompt-wording equivalence tests

#### Slice A3: Deterministic lowering

Create:

- `transform_v48_seed.py`

Freeze:

- `ADEU -> ADEU` transform posture only
- one downstream target only
- deterministic `semantic_normal_form -> taskpack_binding_spec_seed` transform

Required verification:

- deterministic transform tests
- blocked ambiguity tests
- blocked missing-relation tests

#### Slice A4: Downstream bridge

Consume:

- released `V48-A` / `V48-B` surfaces

Add:

- one narrow bridge helper that hands the seed to existing binding/compile flows

Do not include yet:

- broad free-text task authoring
- multi-domain language
- worker execution runtime

### Build Methodology Target

When fully integrated, this module should be gated by:

- `ruff`
- targeted `pytest`
- schema export checks if schema files are committed
- example/fixture regeneration checks only if added as committed fixtures

## Module B: `adeu_symbol_audit`

### Target End State

Target repo home:

- `packages/adeu_symbol_audit/src/adeu_symbol_audit/`
- `packages/adeu_symbol_audit/tests/`
- optional schema home:
  - `packages/adeu_symbol_audit/schema/`
  - `spec/`

Imported bundle reference:

- [examples/external_prototypes/adeu-symbol-audit-v0-bundle](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-symbol-audit-v0-bundle)

### Full Module Goal

Provide a repo-owned read-only audit family with:

- deterministic symbol census
- one-audit-per-symbol semantic audit ledger
- mechanical coverage/closure report

### Concrete Slice Plan

#### Slice B1: Census and coverage only

Create:

- `models.py`
- `census.py`
- `coverage.py`

Freeze:

- symbol kinds included
- symbol identity law
- pilot-scope manifest format
- coverage closure law

Do not include yet:

- semantic SPU claims
- CLI surface
- repo-wide scope

Required verification:

- census determinism tests
- local-function capture tests
- coverage mismatch fail-closed tests

#### Slice B2: Semantic audit ledger

Create:

- `spu.py`

Before shipping B2, decide explicitly whether the semantic/evidence vocabulary:

- reuses Module A semantic primitives
- or is intentionally independent

That decision should be recorded before the repo accepts a second semantic-
normalization idiom.

Freeze:

- audit entry schema
- evidence-ref minimums
- allowed `audit_status` values
- separation between closure truth and semantic uncertainty

Required verification:

- one audit per symbol tests
- low-confidence / unresolved handling tests
- evidence minimum tests

#### Slice B3: CLI or orchestration surface

Create only after B1/B2 are accepted:

- `cli.py` or equivalent runner

Required verification:

- CLI golden tests or harness-run tests

### Build Methodology Target

When fully integrated, this module should be gated by:

- `ruff`
- targeted `pytest`
- committed fixture parity tests for sample census/audit/coverage outputs

### Overlap Rule

This module must not silently fork the repo’s symbol universe.

It should explicitly state:

- what it reuses from `repo_symbol_catalog@1`
- what it extends beyond it
- why any new symbol-kind additions are justified

## Module C: `adeu_odeu_sim`

### Target End State

Target repo home:

- kernel package:
  - `packages/adeu_odeu_sim/src/adeu_odeu_sim/`
  - `packages/adeu_odeu_sim/tests/`
- later API consumer:
  - `apps/api/src/adeu_api/odeu_sim.py` or equivalent bounded route module
- later web consumer:
  - `apps/web/src/app/odeu-sandbox/`

Imported bundle reference:

- [examples/external_prototypes/odeu-sandbox-app](/home/rose/work/LexLattice/odeu/examples/external_prototypes/odeu-sandbox-app)

### Full Module Goal

Provide a repo-owned ODEU simulation kernel with:

- typed state models
- typed actions
- typed scenarios
- typed metrics
- deterministic update loop

Later consumers may expose:

- API access
- browser UI

### Concrete Slice Plan

#### Slice C1: Kernel-only package

Create:

- `models.py`
- `actions.py`
- `scenarios.py`
- `regimes.py`
- `metrics.py`
- `engine.py`

Freeze:

- pilot ontology
- lane-crossing contracts
- starter scenario set
- regime output schema

Do not include yet:

- FastAPI
- browser UI
- persistent storage

Required verification:

- deterministic engine tests
- scenario regression tests
- metrics consistency tests

#### Slice C2: API surface

Only after kernel acceptance:

- add one bounded API route
- keep it read-only and fixture-first

Required verification:

- API response tests
- schema/shape parity tests

#### Slice C3: UI surface

Only after kernel and API acceptance:

- add one bounded web route or app surface

Required verification:

- route smoke tests
- minimal interaction tests

### Build Methodology Target

When fully integrated, this module should be gated by:

- `ruff`
- targeted `pytest` for kernel first
- later API/UI checks only when those surfaces actually land

## Module D: `adeu_paper_semantics`

### Target End State

Target repo home:

- semantic contract package:
  - `packages/adeu_paper_semantics/src/adeu_paper_semantics/`
  - `packages/adeu_paper_semantics/tests/`
- possible schema export home:
  - `packages/adeu_paper_semantics/schema/`
  - `spec/`
- later web route:
  - `apps/web/src/app/papers/semantic-workbench/`
- later domain/harness integration:
  - `packages/urm_domain_paper/`
  - `packages/urm_domain_adeu/`

Imported bundle reference:

- [examples/external_prototypes/adeu-paper-semantic-workbench-poc](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-paper-semantic-workbench-poc)

This module should be read using two different planning horizons:

- full-module internalization order:
  keep it later, because the total blast radius is high
- schema-only demonstrator order:
  `D1` may move earlier, after `A1` / `A2`, if the repo wants to prove the
  syntax-of-concepts direction on a real paper-domain artifact before taking on the
  full workbench

### Full Module Goal

Provide a repo-owned paper semantic artifact family and, later, a workbench UI over it.

### Concrete Slice Plan

#### Slice D1: Semantic contract only

Create:

- paper semantic artifact models
- worker request contract models
- diagnostics and projection types

Freeze:

- source-authority posture
- advisory-only interpretation posture
- span anchor semantics
- diagnostic kinds

Do not include yet:

- web route
- URM template registration
- spatial 3D view

Required verification:

- schema/export tests
- sample artifact validation tests

#### Slice D2: Read-only mock workbench

Only after D1 acceptance:

- add a bounded web route using mock/sample artifacts only

Required verification:

- route smoke tests
- UI-state tests over committed mock artifacts

#### Slice D3: Worker bridge

Only after D1/D2 acceptance:

- add the live worker request/response bridge
- only through repo-owned harness/domain surfaces

Required verification:

- API/domain template tests
- evidence extraction tests

#### Slice D4: Advanced visualization

Only after the core route is accepted:

- spatial-lane scene
- richer morphic transitions

Required verification:

- bounded frontend tests only

### Build Methodology Target

When fully integrated, this module should be gated by:

- `ruff`
- targeted `pytest`
- schema export checks
- route smoke tests once the route exists

## Acceptance Standard For “Full Module”

A prototype should only be considered aligned as a full repo module once all of the
following are true:

1. it lives in repo-owned package or app paths
2. its core contracts are documented by repo-owned planning/lock artifacts
3. its tests run through repo-native tooling
4. its accepted shipped scope is narrower than or equal to what the repo actually wires
5. the original imported intake pack is no longer the primary authority for the module

## Recommended Immediate Next Move

If you want to start internalization now, the most concrete next action is:

1. select `adeu_semantic_forms` as the first candidate
2. draft one bounded internal starter bundle for `Slice A1`
3. keep the other three prototypes intake-only until that first slice lands cleanly
