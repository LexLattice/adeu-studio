# Draft Next Arc Options v86

Status: planning draft after the semantic-declaration / canonical-lookup
frontier and after support-layer v16/v17 Program ODEU methodology reviews.

Authority layer: planning.

This draft records the next candidate family after semantic declaration and
canonical lookup become reviewable. It does not authorize ontology generation,
semantic adjudication, obligation expansion into implementation work, probe
execution, code edits, worker dispatch, runtime transition, product authority,
graph-memory authority, recursive policy amendment, PR creation, commit, merge,
release, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

This selector treats the semantic declaration / canonical lookup family as the
immediate upstream pressure: declaration and lookup can identify an obligation
family, but lookup is not obligation traversal and is not implementation
authority.

## Current Frontier

The support-layer ProgramBench experiments exposed a repeatable failure mode:

```text
post-hoc audit identifies the right parent discriminator
  -> worker receives prose rules
  -> worker patches representative branches
  -> sibling obligations remain untraversed
```

The v16/v17 support docs propose the missing mechanism:

```text
semantic adjudication selects relevant parent classes
  -> deterministic broker imports child obligations
  -> every required child must be closed, deferred, blocked, or proved irrelevant
  -> broker emits the next descent frontier
  -> implementation handoff is blocked until the selected subtree has the
     required closure posture
```

Primary support inputs:

- `docs/support/v16_meta_program_operationalization_robustness_patch.md`
- `docs/support/v17_deterministic_hierarchical_meta_ontology_enforcement.md`
- `docs/support/principled_recursive_odeu_meta_program_experimental_v15.md`
- `docs/support/principled_recursive_odeu_meta_program_experimental_v14.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Next Planning Question

Should the next family make hierarchical obligation traversal deterministic
after model semantic adjudication, without turning the tool into a semantic
judge, ontology author, implementation planner, or execution authority?

Recommended candidate:

```text
HOB-0:
  Hierarchical Obligation Broker
```

## Family Thesis

`HOB-0` should implement the deterministic broker between an already-defined
meta-ontology catalog and model-authored semantic adjudication rows.

The model owns:

```text
semantic applicability judgment
irrelevance / pass-through / deferral warrant
task-specific interpretation
uncertainty statement
```

The deterministic broker owns:

```text
child-obligation inheritance
missing-node detection
status validity
parent-closure validity
gold/scoped readiness promotion checks
next-frontier emission
batchability checks
```

Controlling invariant:

```text
The broker does not decide what a concept means.

Once the model says a parent class applies, the broker deterministically ensures
that every inherited child obligation is visited, closed, deferred, blocked, or
proved irrelevant before the parent can close.
```

## Recommended Next Pressure

- family / practical arc: `HOB-0`
- proposed name:
  - `HOB-0: Hierarchical Obligation Broker`
- recommended first slice:
  - `HOB-0-A`
- recommended package ownership:
  - `packages/adeu_obligation_broker`
  - schema mirrors under `spec/`
- adjacent future integration:
  - semantic compiler integration can consume broker outputs later;
  - ProgramBench reconstruction can use broker outputs later;
  - neither integration is selected by this planning draft.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `HOB-0-A` | Meta-ontology catalog, activation assessment, inherited obligation ledger, and traversal validation |
| `HOB-0-B` | Closure report, next-frontier emission, probe-matrix plan, and implementation batch contract |
| `HOB-0-C` | Delta attribution ledger, stale-ledger invalidation, integration handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`HOB-0-A` should be the first active slice. Candidate starter surfaces:

- `repo_hierarchical_obligation_catalog@1`
- `repo_obligation_activation_assessment@1`
- `repo_inherited_obligation_ledger@1`
- `repo_obligation_traversal_validation_report@1`
- `repo_obligation_broker_non_authority_guardrail@1`

`HOB-0-A` boundary clarification:

```text
HOB-0-A validates whether supplied catalog, activation, inherited obligation,
status, proof, and readiness-claim rows are structurally admissible. It emits
blockers and deterministic next-frontier rows.

HOB-0-A does not compute full subtree closure/readiness summaries. Full closure
aggregation belongs to HOB-0-B.
```

`HOB-0-B` later surfaces:

- `repo_obligation_closure_report@1`
- `repo_obligation_next_frontier_report@1`
- `repo_obligation_probe_matrix_plan@1`
- `repo_obligation_implementation_batch_contract@1`
- `repo_obligation_operationalization_report@1`

`HOB-0-C` later surfaces:

- `repo_obligation_delta_attribution_ledger@1`
- `repo_obligation_stale_ledger_invalidation_report@1`
- `repo_obligation_broker_integration_handoff@1`
- `repo_obligation_broker_family_closeout_alignment@1`

## Non-Authority Boundary

`HOB-0` may:

- validate a fixed numbered meta-ontology catalog shape;
- validate model-authored activation/adjudication rows;
- expand activated parent nodes into inherited child obligations;
- detect missing child rows;
- reject invalid irrelevance, pass-through, deferral, or closure claims;
- emit deterministic next-descent frontier rows;
- emit scoped/gold readiness blockers;
- plan bounded implementation batches from closed or near-closed subtrees;
- attribute observed failure pressure to numbered nodes when supplied with
  explicit attribution rows.

`HOB-0` may not:

- decide that a parent ontology class applies;
- invent or revise the meta-ontology catalog by itself;
- inspect source code to decide semantic meaning;
- generate probes from freeform prose without catalog/ledger rows;
- execute probes or commands;
- dispatch workers;
- implement code;
- grant implementation authority;
- grant product or runtime authority;
- promote scoped readiness to gold readiness without child-closure evidence;
- treat official benchmark failures as clean first-pass evidence;
- select future families.

## `HOB-0-A` Output Contract

`HOB-0-A` should output only:

1. fixed catalog records;
2. activation/adjudication records supplied by a model or upstream semantic
   review;
3. inherited obligation ledgers generated from selected parents;
4. traversal validation reports;
5. next-descent frontier rows for missing, open, blocked, or invalid children;
6. non-authority guardrails;
7. deferred handoff notes for `HOB-0-B` and `HOB-0-C`.

It should not output:

- probe matrices;
- implementation batch contracts;
- worker taskpacks;
- code patches;
- command execution logs;
- product decisions;
- full closure/readiness summaries;
- score-delta attribution;
- official-eval claims;
- future-family selection.

## Core Validation Expectations

`HOB-0-A` should fail closed when:

- a selected parent node has no catalog entry;
- a supplied ledger does not bind to one catalog id, version, hash, and
  authority posture;
- a selected parent has child nodes missing from the inherited ledger;
- a child is omitted without an allowed irrelevance/pass-through proof;
- a scoped deferral is represented as proof of irrelevance;
- a proof-sensitive status lacks its required proof object;
- a parent is marked closed with open required children;
- a gold-ready posture is claimed while any inherited child is scoped-deferred,
  blocked, missing, or representative-only;
- a `not_inherited` row appears where the catalog default or inactive parent
  does not permit it;
- an `optional_observed` row is used to close a parent without local triggering
  or explicit promotion;
- a node status uses unknown vocabulary;
- a node reference is duplicated or ambiguous;
- an activation assessment lacks a warrant.

Recommended `HOB-0-A` acceptance fixtures:

```text
1. parent applies -> children inherited deterministically
2. missing child -> validation fails closed
3. scoped deferral + parent gold-ready claim -> validation fails
4. proved_irrelevant without proof object -> validation fails
5. unknown status vocabulary -> validation fails
6. open/blocked child -> deterministic frontier row emitted
7. shuffled input order -> canonical output order and hash remain stable
```

## Why This Is General

The family is not ProgramBench-specific. It applies to any domain where:

```text
semantic adjudication activates a parent concept
  -> activation should import child obligations
  -> child obligations must be discharged before closure
```

Program reconstruction is only the current stress test. The same broker pattern
can later apply to UX decomposition, architecture review, policy analysis,
workflow activation, resident-agent handoffs, and any structured task where
model judgment selects a class but deterministic traversal must enforce the
method.

## Recommended Selection

Select:

```text
HOB-0: Hierarchical Obligation Broker
```

as the next family, and select `HOB-0-A` as the next default candidate.

After `HOB-0-A` is released and closed, continue the selected `HOB-0` family and
select `HOB-0-B` as the next default candidate.

After `HOB-0-B` is released and closed, continue the selected `HOB-0` family and
select `HOB-0-C` as the next default candidate.

After `HOB-0-C` is released and closed, the selected `HOB-0` family is closed
as deterministic hierarchical obligation brokerage.

The reason is narrow and practical:

```text
Semantic declaration and canonical lookup can identify an obligation family.
They do not ensure that the activated subtree is fully traversed.

HOB-0 adds the missing deterministic traversal broker.
```
