# Draft Checker Fact Bundle Spec v0

Status: working bounded companion draft for authoritative normative markdown.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
- `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`

## 1. Direct Answer

The ANM / `D@1` family needs a first-class checker fact-bundle artifact.

That artifact should carry typed observed facts with provenance.

It should be the bridge between checker execution and evaluator input.

## 2. Core Thesis

The checker fact bundle should answer:

- what subject was observed;
- what fact kind was observed;
- what value or relationship was observed;
- what carrier and provenance mode supported that observation;
- which checker emitted the fact.

It must not answer:

- whether policy passed;
- whether an obligation exists;
- whether a waiver or deferral is valid.

## 3. Fact-Only Checker Posture

Checkers remain fact-only.

They may:

- inspect carriers;
- extract values;
- report direct, indirect, absent, or inconclusive provenance;
- emit typed fact rows.

They may not:

- define clause meaning;
- decide compliance;
- mint obligations;
- mint waiver or deferral authority.

## 4. Minimum Bundle Shape

The first bounded fact-bundle shape should likely carry:

- `schema`
- `bundle_id`
- `scope_snapshot`
- `checker_profile`
- `facts`

Each fact row should likely carry at least:

- `fact_id`
- `subject_ref`
- `fact_type`
- `path` or equivalent target field when applicable
- `values` or equivalent observed payload
- `provenance`
- `checker_id`
- `emitted_at`

The provenance object should likely carry:

- `carrier_ref`
- `mode`
- optional `notes`

## 5. Fact Kinds

Illustrative starter fact kinds are:

- `value_observation`
- `binding_observation`
- `carrier_read`
- `path_presence_observation`
- `path_cardinality_observation`
- `explicit_carriage_observation`

These are candidate starter kinds, not frozen schema IDs.

## 6. Relationship To Neighbor Artifacts

### 6.1 Relation to `D-IR`

`D-IR` defines the normalized semantics that evaluator logic consumes.

The fact bundle provides observed facts only.

So:

- facts do not define policy semantics;
- facts may satisfy or fail to satisfy predicate-contract evidence expectations;
- fact bundles do not replace `D-IR`.

### 6.2 Relation to predicate contracts

Predicate contracts define:

- what evidence kinds are admissible;
- what truth conditions exist;
- what evidence-failure and resolution-failure postures exist.

Fact bundles should therefore provide the raw typed material those contracts expect.

### 6.3 Relation to evaluator results

Evaluator results consume:

```text
D-IR x checker facts x predicate contracts x scope
```

The fact bundle is an input to evaluation, not a result.

## 7. Non-Goals

The first checker-fact bundle slice should not:

1. decide policy compliance;
2. replace predicate contracts;
3. replace result sets;
4. become a generic event log for unrelated runtime telemetry.

## 8. Machine-Checkable Seed Summary

```json
{
  "schema": "checker_fact_bundle_seed@1",
  "artifact": "docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "fact_only_checker_posture_required": true,
  "bundle_id_required": true,
  "scope_snapshot_required": true,
  "checker_profile_required": true,
  "typed_fact_rows_required": true,
  "provenance_required": true,
  "policy_semantics_ownership_forbidden": true,
  "obligation_minting_forbidden": true
}
```
