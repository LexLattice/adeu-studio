# Draft Predicate Contracts Bootstrap Spec v0

Status: working bounded companion draft for authoritative normative markdown.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`

## 1. Direct Answer

The first ANM / `D@1` slice needs an explicit bootstrap predicate-contract artifact.

Without it, predicates such as:

- `bind_to`
- `present`
- `explicit`
- `cardinality_eq`

will drift between prose, evaluator code, and checker assumptions.

That is too soft for a governance-bearing substrate.

## 2. Core Thesis

Predicate contracts are the semantic bridge between:

- source-level clause expressions;
- normalized IR predicate refs;
- checker fact expectations;
- evaluator truth conditions.

They should therefore be explicit typed objects rather than folklore.

## 3. Bootstrap-Only Role

This artifact should be read as bootstrap-only.

Long-term ADEU ownership should move toward:

- O-owned selector handles;
- E-owned predicate contracts for epistemic predicates such as `explicit(path)`.

But the first bounded slice still needs a bootstrap contract layer so v0 does not hide
semantic law inside implementation code.

## 4. Minimum Artifact Role

The bootstrap predicate-contract artifact should likely define, per predicate:

- `predicate_id`
- `owner_layer`
- `version`
- `argument_schema`
- `required_evidence_kinds`
- `truth_conditions`
- `evidence_failure_conditions`
- `resolution_failure_conditions`
- `notes`

This is enough to make bootstrap semantics inspectable without pretending the long-term
O/E split is already solved.

## 5. Candidate Bootstrap Predicates

Illustrative initial predicates are:

- `bind_to`
- `present`
- `explicit`
- `cardinality_eq`

The important distinction is:

- the dialect may reference these predicates;
- the evaluator may apply their contracts;
- the checkers still only emit facts.

Checkers do not own predicate truth conditions.

## 6. Recommended Contract Shape

A bounded v0 predicate contract should look like:

```text
PredicateContract_v0 :=
  {
    predicate_id: string,
    owner_layer: "bootstrap",
    version: string,
    argument_schema: ContractArgument_v0[],
    required_evidence_kinds: string[],
    truth_conditions: TruthCondition_v0[],
    evidence_failure_conditions: FailureCondition_v0[],
    resolution_failure_conditions: FailureCondition_v0[],
    notes?: string
  }

ContractArgument_v0 :=
  {
    name: string,
    kind: "path_ref" | "literal_int" | "anchor_ref",
    required: boolean
  }
```

The purpose of this shape is not to create a proof system.

The purpose is to make bootstrap predicate semantics inspectable enough that:

- the dialect can reference them;
- `D-IR` can point to them;
- checkers know what evidence kinds are admissible;
- evaluators know what counts as true, false, evidence failure, and resolution
  failure.

## 7. Mini-Contracts

### 7.1 `present(path)`

Recommended bounded v0 posture:

- argument schema:
  - `path : path_ref`
- required evidence kinds:
  - `subject_snapshot`
  - `path_presence_observation`
  - `path_cardinality_observation`
- truth conditions:
  - `true` when subject binding resolved, path resolves safely, and cardinality(path)
    is at least `1`
  - `false` when subject binding resolved, path resolves safely, and cardinality(path)
    is `0`
- evidence failure:
  - `unknown_evidence` when subject and path resolved but admissible evidence cannot
    establish presence
- resolution failure:
  - `unknown_resolution` when subject binding cannot be resolved
  - `unknown_resolution` when the path cannot be resolved safely against the subject

### 7.2 `explicit(path)`

Recommended bounded v0 posture:

- argument schema:
  - `path : path_ref`
- required evidence kinds:
  - `subject_snapshot`
  - `path_presence_observation`
  - `explicit_carriage_observation`
- truth conditions:
  - `true` when subject binding resolved, path resolves safely, and the value is
    directly and explicitly carried
  - `false` when the value is absent
  - `false` when the value exists only by defaulting, inheritance, reconstruction,
    implication, or similar non-explicit derivation
- evidence failure:
  - `unknown_evidence` when subject and path resolved but admissible evidence cannot
    determine explicit carriage
- resolution failure:
  - `unknown_resolution` when subject binding cannot be resolved
  - `unknown_resolution` when the path cannot be resolved safely against the subject

### 7.3 `cardinality_eq(path, 1)`

Recommended bounded v0 posture:

- argument schema:
  - `path : path_ref`
  - `expected : literal_int`
- required evidence kinds:
  - `subject_snapshot`
  - `path_cardinality_observation`
- truth conditions:
  - `true` when subject binding resolved, path resolves safely, and
    `cardinality(path) == expected`
  - `false` when subject binding resolved, path resolves safely, and
    `cardinality(path) != expected`
- evidence failure:
  - `unknown_evidence` when exact cardinality cannot be established
- resolution failure:
  - `unknown_resolution` when subject binding cannot be resolved
  - `unknown_resolution` when the path cannot be resolved safely against the subject

### 7.4 `bind_to(anchor)`

Recommended bounded v0 posture:

- argument schema:
  - `anchor : anchor_ref`
- required evidence kinds:
  - `subject_identity_observation`
  - `anchor_value_observation`
  - `binding_observation`
- truth conditions:
  - `true` when subject binding resolved, anchor resolves to exactly one value, and
    admissible evidence establishes that the subject is explicitly bound to that value
  - `false` when subject binding resolved, anchor resolves to exactly one value, and
    admissible evidence establishes that the subject is unbound or bound to a
    different value
- evidence failure:
  - `unknown_evidence` when subject binding and anchor resolution succeeded but
    evidence does not establish whether the binding holds
- resolution failure:
  - `unknown_resolution` when subject binding cannot be resolved
  - `unknown_resolution` when anchor cannot be resolved safely in scope
  - `unknown_resolution` when anchor resolves non-uniquely where uniqueness is
    required

## 8. `EXPLICIT` Boundary

`EXPLICIT path` in source should still lower to `explicit(path)`.

But the bootstrap artifact should make explicit that:

- `explicit(path)` is bootstrap-owned in v0;
- it is expected to migrate later toward E-layer ownership;
- v0 bootstrap semantics distinguish direct carriage from inference, defaults,
  reconstruction, and implication.

That keeps the D-over-E boundary visible even before E owns the predicate formally.

## 9. Failure Posture

The contract layer should also freeze failure posture explicitly.

At minimum it should distinguish:

- truth evaluation failure because evidence was missing or inconclusive;
- resolution failure because subject/path/predicate binding could not be resolved.

That keeps `unknown_evidence` and `unknown_resolution` from being collapsed back into
one ambiguous “unknown”.

## 10. Non-Goals

The first bootstrap predicate-contract slice should not:

1. replace long-term E-layer predicate ownership;
2. let checker executables define policy semantics ad hoc;
3. widen into a general theorem-proving library;
4. imply that all future predicates remain bootstrap-local forever.

## 11. Machine-Checkable Seed Summary

```json
{
  "schema": "predicate_contracts_bootstrap_seed@1",
  "artifact": "docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "bootstrap_predicate_contract_artifact_required": true,
  "predicate_id_required": true,
  "owner_layer_required": true,
  "predicate_version_required": true,
  "argument_schema_required": true,
  "required_evidence_kinds_required": true,
  "truth_conditions_required": true,
  "resolution_failure_conditions_required": true,
  "evidence_failure_conditions_required": true,
  "normalized_contract_shape_required": true,
  "candidate_bootstrap_predicates": [
    "bind_to",
    "present",
    "explicit",
    "cardinality_eq"
  ],
  "checker_semantics_ownership_forbidden": true,
  "long_term_e_or_o_ownership_deferred_but_expected": true
}
```
