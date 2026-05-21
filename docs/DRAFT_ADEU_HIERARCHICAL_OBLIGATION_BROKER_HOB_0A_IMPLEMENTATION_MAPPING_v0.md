# Draft ADEU Hierarchical Obligation Broker HOB-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `HOB-0-A`.

Authority layer: support.

This note maps likely implementation for `HOB-0-A`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment.

## Slice Intent

`HOB-0-A` should make deterministic obligation inheritance reviewable after a
model or upstream process supplies semantic activation rows.

It should answer:

```text
Given this fixed catalog and these activation rows, which child obligations
are inherited, which supplied status/proof rows are invalid, and what is the
next descent frontier?
```

It must not answer:

```text
Should this parent apply?
Is the subtree fully closed?
What probes should run?
What implementation batch should be assigned?
What score changed?
```

## Selected Surfaces

Likely schema / model surfaces:

- `repo_hierarchical_obligation_catalog@1`
- `repo_obligation_activation_assessment@1`
- `repo_inherited_obligation_ledger@1`
- `repo_obligation_traversal_validation_report@1`
- `repo_obligation_broker_non_authority_guardrail@1`

Likely source files:

- `packages/adeu_obligation_broker/pyproject.toml`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/__init__.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/models.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/catalog.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/activation.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/inheritance.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/validation.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/frontier.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/hashing.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/export_schema.py`
- `packages/adeu_obligation_broker/tests/test_hob_0a.py`
- `packages/adeu_obligation_broker/tests/test_obligation_broker_export_schema.py`
- `apps/api/fixtures/obligation_broker/vnext_plus272/`

## Field-Level Expectations

`repo_hierarchical_obligation_catalog@1` should include:

- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `catalog_authority`
- `node_rows`
- `closure_policy_rows`
- `allowed_status_vocabulary`
- `allowed_proof_type_vocabulary`
- `allowed_readiness_vocabulary`
- `shared_vocabulary_ref`

Catalog node rows should include:

- `node_id`
- `node_label`
- `parent_id`
- `node_kind`
- `child_ids`
- `default_inheritance`
- `allowed_statuses`
- `allowed_irrelevance_proof_types`
- `closure_policy_ref`

`repo_obligation_activation_assessment@1` should include:

- `activation_assessment_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `node_activation_rows`
- `activation_warrant_rows`
- `semantic_judge_posture`
- `tool_semantic_authority_posture`

Activation rows should include:

- `node_id`
- `activation_status`
- `warrant_authority`
- `warrant_text`
- `evidence_refs`

`repo_inherited_obligation_ledger@1` should include:

- `inherited_obligation_ledger_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `activation_assessment_ref`
- `obligation_rows`
- `proof_rows`
- `ledger_hash`
- `stale_catalog_posture`

Obligation rows should include:

- `node_id`
- `inherited_from`
- `inheritance_status`
- `obligation_status`
- `warrant_ref`
- `proof_ref`
- `expected_risk_if_deferred`
- `probe_refs`
- `implementation_owner`

Proof rows should be a discriminated union keyed by `proof_kind`. `proof_text`
alone cannot satisfy a proof-sensitive status.

Common proof row fields should include:

- `proof_ref`
- `proof_kind`
- `proof_type`
- `protected_surfaces`
- `warrant_ref`
- `proof_text`
- `evidence_refs`

Required protected surfaces:

- `stdout`
- `stderr`
- `exit`
- `files`
- `state`
- `row_universe`
- `aggregation_denominator`

Proof variants should include:

- irrelevance proof;
- pass-through proof;
- deferral proof;
- blocking proof.

`repo_obligation_traversal_validation_report@1` should include:

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

`repo_obligation_broker_non_authority_guardrail@1` should include:

- `obligation_broker_non_authority_guardrail_ref`
- `tool_semantic_authority_posture`
- `catalog_mutation_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `worker_dispatch_authority_posture`
- `product_authority_posture`
- `future_family_selection_posture`

## Core API Expectations

The implementation should expose deterministic module APIs equivalent to:

```text
load_catalog(payload) -> HierarchicalObligationCatalog
validate_catalog(catalog) -> ValidationDiagnostics
expand_inherited_obligations(catalog, activation) -> InheritedObligationLedger
validate_obligation_ledger(catalog, activation, ledger) -> TraversalValidationReport
emit_frontier(catalog, activation, ledger, diagnostics) -> FrontierRows
canonical_hash(payload) -> sha256
```

Names may vary if repo conventions prefer different names, but the behavior
should remain this narrow.

## Validation Requirements

`HOB-0-A` should fail closed when:

- selected node is absent from the catalog;
- catalog id/version/hash are missing or mismatched;
- catalog child IDs are duplicate or ambiguous;
- inherited child is missing from the ledger;
- required child has no obligation status;
- proof-sensitive status lacks matching proof row;
- scoped deferral is used as irrelevance proof;
- `not_inherited` is used when catalog default and inactive-parent status do
  not permit it, unless an explicit proof places the child outside the active
  subtree;
- `optional_observed` is used to close a parent without local triggering or
  explicit promotion;
- parent closure claim has open, missing, blocked, representative-only, or
  invalid children;
- gold-ready claim contains scoped deferrals, blocked children, missing
  children, or representative-only children;
- unknown vocabulary appears in status, proof, readiness, or handoff fields.

## Required Fixture Set

The first implementation should include fixture-backed tests for:

```text
parent_applies_inherits_all_children
missing_child_fails_closed
scoped_deferral_blocks_gold_parent
irrelevance_without_proof_fails
unknown_status_vocabulary_fails
open_or_blocked_child_emits_frontier
shuffled_input_keeps_canonical_hash
```

## Deferred

Deferred to `HOB-0-B`:

- full subtree closure aggregation;
- probe-matrix planning;
- implementation batch contracts;
- operationalization equivalence reports;
- stale ledger invalidation as its own report.

Deferred to `HOB-0-C`:

- score/failure delta attribution;
- integration handoff;
- family closeout alignment.

Deferred to later families:

- ProgramBench integration;
- semantic compiler integration;
- probe execution;
- worker taskpack generation;
- implementation authority.
