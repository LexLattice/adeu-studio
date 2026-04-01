# Draft Policy Evaluation Result Set Spec v0

Status: working bounded companion draft for authoritative normative markdown.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md`
- `docs/DRAFT_D1_DIALECT_SPEC_v0.md`
- `docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md`
- `docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md`

## 1. Direct Answer

The ANM / `D@1` family needs a first-class evaluation result-set artifact.

That artifact should record run-specific evaluation outcomes over:

```text
D-IR x checker fact bundle x predicate contracts x scope
```

It should stay distinct from both the checker fact bundle and the obligation ledger.

## 2. Core Thesis

The evaluation result set should answer:

- what clause was evaluated;
- what subject was evaluated, if any;
- what applicability posture held;
- what observed outcome held;
- what effective verdict held;
- what evidence and contracts supported that result.

It should not be treated as:

- compiled policy semantics;
- cross-run current state;
- waiver or deferral authority by itself.

## 3. Minimum Result Shape

The first bounded result-set shape should likely carry:

- `schema`
- `result_set_id`
- `scope_snapshot`
- `d_ir_ref`
- `fact_bundle_ref`
- `predicate_contract_ref`
- `results`

Each result row should likely carry at least:

- `result_id`
- `clause_ref`
- `clause_semantic_hash`
- `subject_ref` when resolved
- `applicability`
- `observed_outcome`
- `effective_verdict`
- `supporting_fact_refs`
- `supporting_contract_refs`
- `message`

## 4. Applicability And Verdict Model

The result-set artifact should preserve the split model from the `D@1` dialect:

- `applicability`:
  - `active`
  - `gated_off`
  - `excepted`
- `observed_outcome`:
  - `not_evaluated`
  - `pass`
  - `fail`
  - `unknown_evidence`
  - `unknown_resolution`
- `effective_verdict`:
  - `pass`
  - `fail`
  - `waived`
  - `deferred`
  - `gated_off`
  - `unknown_evidence`
  - `unknown_resolution`

This artifact is the authoritative home for run-specific result posture.

## 5. Relation To The Ledger

The result set is immutable and run-specific.

The ledger is mutable and cross-run.

So:

- result sets preserve what happened in one evaluation run;
- the ledger projects current operational state across runs;
- the ledger may join back to result rows through `latest_result_run`,
  `first_seen_run`, and related linkage fields.

Important boundary:

- a result set may contain clause-scope blocking `unknown_resolution` rows even when
  no `subject_ref` was formed;
- the ledger must not fabricate a row for that case.

## 6. Relation To Checker Facts And `D-IR`

`D-IR` provides normalized clause meaning.

The checker fact bundle provides observed facts only.

The result set is where those inputs are actually evaluated together.

That means:

- result sets consume `D-IR` and facts;
- result sets do not replace `D-IR`;
- result sets do not replace the fact bundle.

## 7. Non-Goals

The first result-set slice should not:

1. replace the ledger;
2. replace `D-IR`;
3. decide waiver or deferral authority by itself;
4. become a generic run log for unrelated runtime behavior.

## 8. Machine-Checkable Seed Summary

```json
{
  "schema": "policy_evaluation_result_set_seed@1",
  "artifact": "docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "run_specific_result_artifact_required": true,
  "d_ir_ref_required": true,
  "fact_bundle_ref_required": true,
  "predicate_contract_ref_required": true,
  "applicability_required": true,
  "observed_outcome_required": true,
  "effective_verdict_required": true,
  "ledger_replacement_forbidden": true,
  "clause_scope_unknown_resolution_without_ledger_row_supported": true
}
```
