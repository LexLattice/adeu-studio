# Draft Authoritative Normative Markdown Spec v0

Status: working high-level draft for a separate but connected infra direction.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not select the next family by itself;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v0.md`
- `docs/support/DRAFT_ANM_D1_ARC30_SOURCE_SEED_v1.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`
- released `V45-A` through `V45-F` repo self-description baseline on `main`

## 1. Direct Answer

ADEU should add a markdown-native normative substrate with an explicit authoritative
sub-language rather than continuing to rely on prose-only obligation capture.

The core move is:

- keep ordinary markdown prose readable and non-inferred;
- make authority opt-in through fenced `D@1` blocks;
- compile those blocks into typed normalized semantics;
- evaluate them against checker facts;
- track live obligations in a first-class ledger.

The problem is not markdown expressiveness.

The problem is that prose interleaves explanation and obligation too loosely for
reliable agentic execution.

## 2. Core Thesis

This direction should separate five things that are currently too easy to blur:

1. human-readable prose;
2. normative source clauses;
3. normalized compiled semantics;
4. observed checker facts;
5. live operational obligation state.

That gives a cleaner pipeline:

```text
authoring markdown
  -> authoritative D blocks
  -> normalized D-IR
  -> checker fact bundles
  -> evaluation result sets
  -> obligation ledger
```

The first safe version should remain small:

- markdown-native container;
- one bounded deontic dialect;
- fact-only checkers;
- one obligation ledger;
- bootstrap predicate contracts where O/E ownership does not yet exist.

## 3. Why This Is A Separate Arc Direction

This direction is connected to the completed `V45` self-description branch, but it
should not be collapsed into it.

`V45` asked:

- what does the ADEU repo currently contain?
- how are repo surfaces typed descriptively?
- what descriptive outputs should later governance consume?

This direction asks:

- how should ADEU encode authoritative obligations inside markdown?
- how should those obligations compile into machine-checkable semantics?
- how should live obligations be tracked across runs and closeout?

So this direction may constrain:

- how future locks or policy-bearing docs are written;
- how later recursive-governance consumers express admissibility rules;
- how descriptive outputs from `V45` are consumed normatively.

But it should not mint:

- direct mutation entitlement;
- recursive execution authority;
- automatic supersession of current lock/planning markdown;
- repo-wide migration of all docs by this seed alone.

## 4. Relationship To `V45` / `v28`

`V45` and this proposed direction are complementary.

`V45` now provides the bounded descriptive substrate on `main`:

- entity and schema-family surfaces;
- symbol and dependency surfaces;
- arc dependency posture;
- test-intent visibility;
- optimization diagnostics;
- descriptive-to-normative binding doctrine.

This proposed direction would provide the normative authoring and compilation
substrate that later consumers can use to express governance-bearing rules with less
prose ambiguity.

The clean relation is:

- `V45` emits typed descriptive objects;
- this direction emits typed normative source, IR, and obligation-state objects;
- later consumers may bind the two together.

This should not be read as a `V45` continuation.

It is a separate infra family candidate.

## 5. Coexistence With Current Markdown Doctrine

The current repo already has lock, planning, architecture, and support docs with active
authority roles.

This direction should therefore start with explicit coexistence rules.

### 5.1 No prose inference outside authority blocks

The compiler should never recover obligations from arbitrary prose paragraphs or bullet
lists.

Only explicitly authoritative `D@1` surfaces should compile into normative semantics.

### 5.2 Migration should remain opt-in

The first release should support at least two postures:

- standalone ANM policy docs;
- companion ANM docs that sit beside existing prose docs.

Repo-wide conversion of existing lock/planning docs should remain deferred.

### 5.3 Existing markdown authority remains live

Until an explicit later migration rule is selected:

- existing prose lock docs remain lock-authoritative;
- existing planning docs remain planning-authoritative;
- ANM/D@1 docs do not silently override them by existing.

## 6. Recommended First Artifact Family

The first bounded family should likely introduce or prepare:

- one markdown-native ANM source form with fenced `D@1` authority blocks;
- one normalized `D` IR artifact;
- one bootstrap predicate-contract artifact;
- one checker fact-bundle artifact;
- one evaluator result-set artifact;
- one policy obligation-ledger artifact.

Illustrative candidate artifact names are:

- `d1_normalized_ir@1`
- `predicate_contracts_bootstrap@1`
- `checker_fact_bundle@1`
- `policy_evaluation_result_set@1`
- `policy_obligation_ledger@1`

These are planning-level candidate names, not frozen schema IDs.

## 7. Artifact Boundary Matrix

The family boundary should remain explicit.

| Artifact | Does | Must not do |
|---|---|---|
| ANM source markdown | container for readable prose plus authoritative fenced blocks | must not cause policy inference from prose outside `D@1` |
| `D@1` dialect source blocks | authoritative normative source clauses with selectors, assertions, and qualifiers | must not be confused with normalized IR, checker facts, result sets, or ledger state |
| normalized `D-IR` | normalized semantic projection of authoritative `D@1` clauses | must not store markdown formatting, checker facts, run verdicts, or ledger state |
| checker fact bundle | typed observed facts emitted by fact-only checkers | must not define policy semantics or mint obligations |
| evaluator result set | run-specific evaluation of `D-IR` against facts and contracts | must not replace the ledger's cross-run current-state role |
| obligation ledger | cross-run current-state projection of instantiated obligation rows | must not mint policy authority, waiver authority, or deferral authority by itself |
| bootstrap predicate contracts | explicit bootstrap semantics for predicate identity, arguments, required evidence, and failure posture | must not be hidden inside checker code or widened into a general theorem-proving surface |

## 8. First Safe Family Shape

The safe first move should stop at bounded normative compilation and obligation-state
tracking.

That means:

- typed clause parsing;
- normalized IR;
- typed checker facts;
- typed evaluation results;
- first-class ledger over instantiated obligations;
- explicit bootstrap-only selector and predicate posture.

It should stop before:

- theorem proving;
- general boolean logic;
- imported O-owned selector handles;
- imported E-owned predicate registries;
- automatic waiver or deferral issuance;
- direct execution authority.

## 9. Non-Goals

This direction should not initially aim to:

1. formalize arbitrary prose outside `D@1`;
2. replace ordinary markdown explanation with fully formal text;
3. reopen or silently supersede existing `V45` artifacts;
4. authorize mutation, scheduling, or recursive execution;
5. force repo-wide migration of current docs into ANM immediately.

## 10. Suggested Follow-On Docs

If this direction is selected for next-arc planning, the first bundle should probably
include:

- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
- `docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md`
- `docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md`
- `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`
- `docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md`
- one later artifact-family or schema bundle draft once the first set is stable

## 11. Machine-Checkable Seed Summary

```json
{
  "schema": "authoritative_normative_markdown_seed@1",
  "artifact": "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "separate_from_v45_but_connected": true,
  "v45_consumed_as_descriptive_substrate_only": true,
  "markdown_native_container_required": true,
  "authoritative_dialect_blocks_required": true,
  "no_prose_obligation_inference_required": true,
  "normalized_ir_required": true,
  "fact_only_checker_model_required": true,
  "checker_fact_bundle_required": true,
  "policy_evaluation_result_set_required": true,
  "obligation_ledger_required": true,
  "bootstrap_predicate_contract_artifact_required": true,
  "artifact_boundary_matrix_required": true,
  "companion_or_standalone_adoption_posture_required": true,
  "repo_wide_doc_migration_initially_deferred": true,
  "mutation_or_recursive_execution_authority_forbidden_here": true,
  "candidate_artifacts": [
    "d1_normalized_ir@1",
    "predicate_contracts_bootstrap@1",
    "checker_fact_bundle@1",
    "policy_evaluation_result_set@1",
    "policy_obligation_ledger@1"
  ]
}
```
