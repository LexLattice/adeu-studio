# LOCKED_CONTINUATION_vNEXT_PLUS272

## Status

Bounded starter lock draft for `HOB-0-A` (catalog, activation assessment,
inherited obligation ledger, traversal validation, next-frontier rows, and
non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`HOB-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `HOB-0`
- slice: `HOB-0-A`
- branch-local execution target: `arc/hob-0-a`

## Purpose

Freeze the bounded `HOB-0-A` starter slice so the repo can make hierarchical
obligation inheritance deterministic after semantic adjudication, without
turning the broker into a semantic judge, ontology author, probe executor,
implementation planner, worker dispatcher, or product authority.

`vNext+272` authorizes docs plus the next implementation path over a new
repo-owned obligation-broker package. It does not authorize semantic
adjudication, ontology generation, catalog mutation by the tool, probe
execution, command execution, worker dispatch, implementation batches, code
patches outside the slice package, runtime transition, product authorization,
graph-memory authority, official benchmark scoring, future-family selection,
release authority, or recursive policy amendment.

Controlling invariant:

```text
Model-supplied activation can say a parent node applies.

The broker may then deterministically import that parent node's child
obligations, validate every inherited child status/proof row, reject false
parent closure, and emit the next descent frontier.

The broker may not decide whether the parent should have applied.
```

## Instantiated Here

- `HOB-0-A` instantiates the first deterministic traversal-broker seam:
  - new repo-owned package:
    - `adeu_obligation_broker`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
    - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
    - `docs/support/v16_meta_program_operationalization_robustness_patch.md`
    - `docs/support/v17_deterministic_hierarchical_meta_ontology_enforcement.md`
    - `docs/support/principled_recursive_odeu_meta_program_experimental_v15.md`
    - `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
    - `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
  - emitted starter record shapes:
    - `repo_hierarchical_obligation_catalog@1`
    - `repo_obligation_activation_assessment@1`
    - `repo_inherited_obligation_ledger@1`
    - `repo_obligation_traversal_validation_report@1`
    - `repo_obligation_broker_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `repo_hierarchical_obligation_catalog@1` fields:

- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `catalog_authority`
- `node_rows`
- `allowed_status_vocabulary`
- `allowed_proof_type_vocabulary`
- `allowed_readiness_vocabulary`
- `shared_vocabulary_ref`
- `closure_policy_rows`

Minimum catalog node fields:

- `node_id`
- `node_label`
- `parent_id`
- `node_kind`
- `child_ids`
- `default_inheritance`
- `allowed_statuses`
- `allowed_irrelevance_proof_types`
- `closure_policy_ref`

Minimum `repo_obligation_activation_assessment@1` fields:

- `activation_assessment_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `node_activation_rows`
- `activation_warrant_rows`
- `semantic_judge_posture`
- `tool_semantic_authority_posture`

Required activation posture:

- activation rows are model-authored or upstream-authored semantic judgments;
- the broker validates their shape and vocabulary only;
- the broker does not decide semantic applicability.

Minimum `repo_inherited_obligation_ledger@1` fields:

- `inherited_obligation_ledger_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `activation_assessment_ref`
- `obligation_rows`
- `proof_rows`
- `ledger_hash`
- `stale_catalog_posture`

Minimum obligation row fields:

- `node_id`
- `inherited_from`
- `inheritance_status`
- `obligation_status`
- `warrant_ref`
- `proof_ref`
- `expected_risk_if_deferred`
- `probe_refs`
- `implementation_owner`

Minimum structured proof rows:

- all proof rows are a discriminated union keyed by `proof_kind`;
- `proof_text` alone can never satisfy a proof-sensitive status.

Common proof row fields:

- `proof_ref`
- `proof_kind`
- `proof_type`
- `protected_surfaces`
- `warrant_ref`
- `proof_text`
- `evidence_refs`

Required `protected_surfaces` keys:

- `stdout`
- `stderr`
- `exit`
- `files`
- `state`
- `row_universe`
- `aggregation_denominator`

- irrelevance proof:
  - `proof_type`
  - `protected_surfaces`
  - `warrant_ref`
  - `proof_text`
  - `evidence_refs`
- pass-through proof:
  - `pass_through_scope`
  - `protected_surfaces`
  - `warrant_ref`
  - `proof_text`
  - `evidence_refs`
- deferral proof:
  - `deferral_kind`
  - `expected_risk`
  - `handoff_effect`
  - `warrant_ref`
  - `proof_text`
- blocking proof:
  - `blocker_kind`
  - `required_next_evidence`
  - `affected_surfaces`
  - `warrant_ref`

Minimum `repo_obligation_traversal_validation_report@1` fields:

- `traversal_validation_report_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `activation_assessment_ref`
- `inherited_obligation_ledger_ref`
- `validation_status`
- `diagnostic_rows`
- `frontier_rows`
- `parent_closure_claim_rows`
- `readiness_claim_rows`
- `canonical_output_hash`

Required frontier row fields:

- `node_id`
- `reason`
- `required_next_action`
- `blocking_parent_refs`
- `diagnostic_ref`

Minimum `repo_obligation_broker_non_authority_guardrail@1` fields:

- `obligation_broker_non_authority_guardrail_ref`
- `tool_semantic_authority_posture`
- `catalog_mutation_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `worker_dispatch_authority_posture`
- `product_authority_posture`
- `future_family_selection_posture`

## Required Implementation Behavior

`HOB-0-A` must provide deterministic functions or equivalent module APIs that:

1. validate catalog shape and duplicate/ambiguous node references;
2. validate activation assessments against the catalog id/version/hash;
3. expand selected parent nodes into inherited child obligations;
4. validate supplied obligation rows and proof rows;
5. reject invalid parent closure/readiness claims;
6. emit deterministic next-frontier rows for missing, open, blocked, or invalid
   inherited children;
7. canonicalize output order and hashes regardless of input row order.

`HOB-0-A` must fail closed when:

- a selected parent node is absent from the catalog;
- catalog id/version/hash are missing or mismatched;
- an inherited child is missing from the ledger;
- a child is omitted without an allowed proof object;
- a proof-sensitive status lacks its structured proof row;
- a scoped deferral is used as irrelevance proof;
- `not_inherited` is used without an inactive parent, catalog default
  allowance, or explicit outside-active-subtree proof;
- `optional_observed` is used to close a parent without local triggering or
  explicit promotion;
- a parent closure claim has open, missing, blocked, representative-only, or
  invalid children;
- a gold-ready claim contains scoped deferrals, blocked children, missing
  children, or representative-only children;
- unknown vocabulary appears in status, proof, readiness, or handoff fields.

## Required Starter Fixtures

The first implementation must include deterministic fixtures covering:

```text
1. parent applies -> all children inherited
2. missing child -> validation fails closed
3. scoped deferral + parent gold-ready claim -> validation fails
4. proved_irrelevant without proof object -> validation fails
5. unknown status vocabulary -> validation fails
6. open or blocked child -> deterministic frontier row emitted
7. shuffled input order -> canonical output order and hash are stable
```

## Deferred To Later Slices

Deferred to `HOB-0-B`:

- full subtree closure/readiness summary computation;
- probe-matrix planning;
- implementation batch contracts;
- operationalization reports;
- stale-ledger invalidation beyond catalog mismatch diagnostics.

Deferred to `HOB-0-C`:

- score/failure delta attribution;
- integration handoff rows;
- stale-ledger invalidation as a standalone report;
- family closeout alignment.

Deferred to later families:

- ProgramBench-specific integration;
- semantic compiler integration;
- probe execution;
- worker taskpack generation;
- implementation authority.

## Validation Command Expectation

Before implementation PR, run the repo Python lane gate:

```text
make check
```

If the implementation remains docs/artifacts-only, the active arc starter gate
may use the docs-only shortcut, but any Python package/schema/test change must
use `make check`.

## Machine-Checkable Contract Seed

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+272",
  "target_path": "HOB-0-A",
  "authority_layer": "lock",
  "selected_family": "HOB-0",
  "selected_slice": "HOB-0-A",
  "selected_record_shapes": [
    "repo_hierarchical_obligation_catalog@1",
    "repo_obligation_activation_assessment@1",
    "repo_inherited_obligation_ledger@1",
    "repo_obligation_traversal_validation_report@1",
    "repo_obligation_broker_non_authority_guardrail@1"
  ],
  "package_scope": "packages/adeu_obligation_broker",
  "semantic_adjudication_authority_granted": false,
  "catalog_mutation_authority_granted": false,
  "probe_execution_authority_granted": false,
  "implementation_batch_authority_granted": false,
  "worker_dispatch_authority_granted": false,
  "product_authority_granted": false,
  "future_family_selection_granted": false,
  "catalog_id_version_hash_required": true,
  "shared_vocabulary_source_required": true,
  "proof_rows_discriminated_union_required": true,
  "frontier_rows_required_for_open_or_blocked_children": true,
  "full_closure_aggregation_deferred_to_hob_0b": true
}
```
