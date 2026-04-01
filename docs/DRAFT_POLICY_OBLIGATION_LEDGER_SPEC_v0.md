# Draft Policy Obligation Ledger Spec v0

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

The ANM / `D@1` stack needs a first-class operational artifact that tracks live
obligation instances across runs.

That artifact should be the obligation ledger.

It should be distinct from:

- source markdown;
- normalized D-IR;
- one-off checker fact bundles;
- one-off evaluator result sets.

## 2. Core Thesis

Compiled clauses are not enough for operational closeout.

The system also needs a persistent bridge that answers:

- which obligations currently exist for this snapshot and scope;
- which ones are satisfied, violated, waived, deferred, or blocked;
- what latest evidence and latest run status exist;
- who owns the open remediation surface.

Without that bridge, agents and closeout flows fall back to raw prose or ephemeral run
outputs.

## 3. Ledger Identity

Each ledger row should correspond to:

```text
(clause semantic identity) x (resolved subject) x (work scope / target snapshot)
```

That means the ledger is:

- not just a clause catalog;
- not just a result log;
- not just a fact bundle.

It is the stateful operational projection of instantiated policy obligations.

## 4. Minimum Row Shape

The first bounded row shape should likely carry at least:

- `obligation_id`
- `clause_ref`
- `clause_semantic_hash`
- `subject_ref`
- `scope_snapshot`
- `first_seen_run`
- `latest_result_run`
- `latest_applicability`
- `latest_observed_outcome`
- `latest_effective_verdict`
- `ledger_state`
- `owner`
- `required_evidence`
- `last_fact_refs`
- `waiver_ref`
- `deferral_ref`
- `remediation_ref`
- `updated_at`

The important tightening relative to a looser row model is:

- `latest_applicability` must be preserved;
- `latest_observed_outcome` must be preserved;
- `latest_effective_verdict` alone is not enough.

`gated_off`, `excepted`, `waived`, and `pass` are not interchangeable.

## 5. Ledger State Vocabulary

Illustrative bounded starter states are:

- `satisfied`
- `violated`
- `waived`
- `deferred`
- `gated_off`
- `blocked_unknown_evidence`
- `blocked_unknown_resolution`

These are operational ledger states, not replacements for the evaluation result model.

## 6. Difference From Neighbor Artifacts

### 6.1 Difference from D-IR

D-IR contains:

- compiled clause meaning;
- selector references;
- normalized assertions;
- qualifiers;
- trace metadata.

D-IR should not be overloaded with:

- live owners;
- remediation state;
- waiver linkage;
- latest run status.

### 6.2 Difference from result sets

Result sets are run-specific and mostly immutable.

The ledger is cross-run and stateful.

Result sets answer:

- what happened in one evaluation run.

The ledger answers:

- what obligations are currently open or closed for a scope.

## 7. Waiver And Deferral Boundary

The ledger may record waiver and deferral linkage.

It must not mint waiver or deferral authority by itself.

So the minimum boundary should be:

- `waiver_ref` and `deferral_ref` point to explicit external artifacts only;
- a ledger row may not self-issue a waiver or deferral;
- this draft does not yet freeze the final waiver/deferral artifact family;
- the existence of `waiver_ref` / `deferral_ref` slots is a bridge requirement, not a
  completed waiver doctrine.

## 8. How Agents And Closeout Should Use It

Coding or remediation agents should not start from raw policy prose every time.

They should be able to query the ledger for a target scope and filter to non-closed
rows.

Closeout should not gate on prose or one-off checker output directly.

It should gate on the current live ledger posture plus the current evaluation result
set.

Illustrative strict-closeout rule:

- no `violated`
- no `blocked_unknown_evidence`
- no `blocked_unknown_resolution`
- no `deferred` unless the gate profile explicitly allows it

## 9. Result-Set Mapping

The ledger should not infer its state vocabulary indirectly.

Recommended v0 mapping is:

| Evaluation posture | Ledger state | Row posture |
|---|---|---|
| `pass` | `satisfied` | closed / non-blocking |
| `fail` | `violated` | open / blocking |
| `waived` | `waived` | closed / non-blocking |
| `deferred` | `deferred` | open by default |
| `gated_off` | `gated_off` | non-active / non-blocking |
| `unknown_evidence` | `blocked_unknown_evidence` | open / blocking |
| `unknown_resolution` | `blocked_unknown_resolution` | open / blocking if a subject row exists |

Important boundary:

- if `unknown_resolution` happens before a `subject_ref` can be formed, that remains a
  clause-scope blocking evaluator result and does not fabricate a ledger row.

## 10. Lifecycle Posture

The recommended v0 lifecycle posture is:

```text
mutable current-state rows + audit linkage to immutable result sets
```

That means:

- one current row per obligation identity;
- rows update across runs;
- immutable result sets preserve run history;
- the ledger preserves current state plus linkage to that run history.

### 10.1 Row creation

A row is first created when a clause is instantiated against a resolved subject for a
scope snapshot.

Recommended creation rule:

- create a row on first instantiated result for `pass`, `fail`, `waived`, `deferred`,
  `gated_off`, `unknown_evidence`, or `unknown_resolution`;
- do not create a row when selector expansion is zero-match and no subject instance
  exists;
- do not fabricate a row when resolution failed before `subject_ref` could be formed.

### 10.2 Row updates

A row is updated when a later run over the same obligation identity produces:

- a new evaluation posture;
- new evidence or fact refs;
- a new owner;
- a new remediation ref;
- a new waiver ref;
- a new deferral ref.

### 10.3 Persistence across runs

Rows should persist across runs for the same obligation identity.

A row must not be deleted merely because it became:

- `satisfied`
- `waived`
- `gated_off`

### 10.4 Scope snapshot posture

Recommended interpretation:

- repeated runs against the same scope snapshot update the same rows;
- a new scope snapshot creates a new row space;
- prior-snapshot rows remain historical and queryable under their original scope
  snapshot.

### 10.5 Subject disappearance and reconciliation

Recommended bounded rule:

- if a subject disappears because a new scope snapshot is being evaluated, old rows
  remain untouched as history for the old scope;
- if a previously tracked same-scope row can no longer be reconciled in a later run,
  do not silently delete it; update it to `blocked_unknown_resolution`.

This also applies when a same-scope selector previously instantiated rows but later
goes zero-match.

### 10.6 Minimum audit linkage

To support the lifecycle posture above, a v0 row should also carry:

- `first_seen_run`
- `latest_result_run`
- `updated_at`

## 11. Non-Goals

The first obligation-ledger slice should not:

1. decide compliance by itself;
2. replace D-IR;
3. replace result sets;
4. self-authorize waiver or deferral;
5. become a generic continuation-memory artifact for unrelated work.

## 12. Machine-Checkable Seed Summary

```json
{
  "schema": "policy_obligation_ledger_seed@1",
  "artifact": "docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "first_class_ledger_required": true,
  "row_identity_formula": "clause_semantic_identity_x_subject_x_scope_snapshot",
  "latest_applicability_required": true,
  "latest_observed_outcome_required": true,
  "latest_effective_verdict_required": true,
  "first_seen_run_required": true,
  "ledger_state_vocabulary_required": true,
  "result_set_mapping_required": true,
  "gated_off_state_required": true,
  "waiver_and_deferral_refs_external_only_required": true,
  "mutable_current_state_plus_immutable_result_linkage_required": true,
  "row_creation_on_instantiated_obligation_only_required": true,
  "zero_match_no_first_row_required": true,
  "subject_disappearance_reconciliation_fail_closed_required": true,
  "ledger_self_authorization_forbidden": true,
  "not_generic_hot_memory_artifact": true
}
```
