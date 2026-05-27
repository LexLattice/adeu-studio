# Draft ADEU ODEU Transition Broker OTB-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `OTB-0-A`.

Authority layer: support.

This note maps likely implementation for `OTB-0-A`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment.

## Slice Intent

`OTB-0-A` should make deterministic phase-transition validation reviewable.

It should answer:

```text
Given this phase catalog, bridge contract, artifact set, evidence set,
obligation transfer set, and claimed next phase, is the transition structurally
admissible and what is the next legal frontier?
```

It must not answer:

```text
Is the source phase semantically right?
Is the target phase product-ready?
Which worker should run?
What probes should be executed?
What code should be patched?
```

## Selected Surfaces

Likely schema / model surfaces:

- `repo_phase_circuit_catalog@1`
- `repo_phase_bridge_contract@1`
- `repo_phase_transition_claim@1`
- `repo_phase_transition_validation_report@1`
- `repo_phase_legal_frontier_report@1`
- `repo_transition_broker_non_authority_guardrail@1`

Likely source files:

- `packages/adeu_transition_broker/pyproject.toml`
- `packages/adeu_transition_broker/src/adeu_transition_broker/__init__.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/models.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/vocabulary.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/catalog.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/bridge.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/validation.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/frontier.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/hashing.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/export_schema.py`
- `packages/adeu_transition_broker/tests/test_otb_0a.py`
- `packages/adeu_transition_broker/tests/test_transition_broker_export_schema.py`

## Field-Level Expectations

`repo_phase_circuit_catalog@1` should include:

- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `circuit_authority`
- `phase_rows`
- `transition_rows`
- `allowed_status_vocabulary`
- `shared_vocabulary_ref`

Phase rows should include:

- `phase_id`
- `phase_label`
- `phase_kind`
- `allowed_input_object_kinds`
- `allowed_output_object_kinds`
- `forbidden_evidence_kinds`
- `authority_layer`

Transition rows should include:

- `transition_id`
- `from_phase`
- `to_phase`
- `bridge_contract_ref`
- `transition_kind`
- `default_failure_route`

`repo_phase_bridge_contract@1` should include:

- `bridge_contract_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `transition_id`
- `from_phase`
- `to_phase`
- `O_bridge`
- `E_bridge`
- `D_bridge`
- `U_bridge`
- `bridge_hash`

`O_bridge` should include:

- `required_objects`
- `object_identity_checks`
- `required_artifact_hash_checks`
- `transformation_claims`
- `stale_object_checks`

`E_bridge` should include:

- `required_evidence`
- `forbidden_evidence`
- `evidence_boundary_rules`
- `warrant_requirements`

`D_bridge` should include:

- `obligations_created`
- `obligations_preserved`
- `obligations_discharged`
- `obligations_blocked_or_deferred`
- `forbidden_silent_drops`

`U_bridge` should include:

- `purpose`
- `next_allowed_phases`
- `forbidden_promotions`
- `failure_routes`

`repo_phase_transition_claim@1` should include:

- `transition_claim_ref`
- `claiming_actor_ref`
- `claim_source`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `from_phase`
- `to_phase`
- `transition_id`
- `claimed_transition_kind`
- `claimed_readiness_posture`
- `claimed_evidence_posture`
- `claimed_promotion`
- `artifact_refs`
- `evidence_refs`
- `obligation_transfer_refs`
- `intended_use`
- `requested_next_frontier`
- `claim_hash`

Allowed `claim_source` values should include:

- `orchestrator`
- `worker_closeout`
- `planner`
- `broker_output`
- `manual_review`

Artifact rows consumed by the validator should include:

- `artifact_ref`
- `artifact_kind`
- `source_phase`
- `authority_layer`
- `file_hash`
- `canonical_payload_hash`
- `semantic_object_hash`
- `catalog_hash`
- `bridge_hash`
- `evidence_boundary_hash`
- `obligation_set_hash`
- `object_identity_claim`
- `evidence_refs`
- `freshness_basis`

Evidence rows consumed by the validator should include:

- `evidence_ref`
- `evidence_kind`
- `source_phase`
- `authority_layer`
- `boundary_posture`
- `clean_first_pass_posture`
- `evidence_hash`
- `derived_from_evidence_refs`
- `contamination_tags`

Obligation transfer rows consumed by the validator should include:

- `obligation_ref`
- `source_phase`
- `target_phase`
- `transfer_status`
- `discharge_ref`
- `deferral_ref`
- `blocker_ref`
- `preservation_required`

`repo_phase_transition_validation_report@1` should include:

- `transition_validation_report_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `transition_id`
- `bridge_contract_ref`
- `validation_status`
- `bridge_consistency_status`
- `bridge_completeness_status`
- `diagnostic_rows`
- `frontier_rows`
- `canonical_output_hash`

Allowed `validation_status` values for A should avoid action-authority language.
Use `valid_for_broker_frontier`, `blocked`, `invalid`, `stale`, or
`conflict_isolated`, rather than standalone `ready`, `implementation_ready`,
`gold_ready`, or `official_ready`.

Allowed `bridge_consistency_status` values should include:

- `consistent`
- `inconsistent`
- `unknown_vocabulary`
- `hash_mismatch`

Allowed `bridge_completeness_status` values should include:

- `complete`
- `missing_required_object`
- `missing_required_evidence`
- `missing_obligation_transfer`
- `missing_equivalence`
- `missing_warrant`
- `missing_deferral_risk`

Diagnostic rows should include:

- `diagnostic_ref`
- `bridge_field`
- `diagnostic_kind`
- `severity`
- `message`
- `object_refs`
- `evidence_refs`
- `required_action`

`repo_phase_legal_frontier_report@1` should include:

- `legal_frontier_report_ref`
- `transition_validation_report_ref`
- `frontier_rows`
- `canonical_output_hash`

Frontier rows should include:

- `frontier_ref`
- `transition_id`
- `frontier_reason`
- `required_next_action`
- `authority_posture`
- `target_phase_constraint`
- `requested_posture`
- `maximum_supported_posture`
- `downgrade_basis`
- `required_revalidation_frontier`

`repo_transition_broker_non_authority_guardrail@1` should include:

- `transition_broker_non_authority_guardrail_ref`
- `semantic_authority_posture`
- `domain_ontology_authority_posture`
- `hob_closure_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `worker_dispatch_authority_posture`
- `product_authority_posture`
- `future_family_selection_posture`

## Core API Expectations

The implementation should expose deterministic module APIs equivalent to:

```text
load_phase_catalog(payload) -> PhaseCircuitCatalog
validate_phase_catalog(catalog) -> ValidationDiagnostics
load_bridge_contract(payload) -> PhaseBridgeContract
validate_bridge_contract(catalog, bridge) -> ValidationDiagnostics
validate_transition(catalog, bridge, transition_claim, artifacts, evidence,
  obligations)
  -> PhaseTransitionValidationReport
emit_legal_frontier(validation_report) -> PhaseLegalFrontierReport
canonical_hash(payload) -> sha256
```

Names may vary if repo conventions prefer different names, but behavior should
remain this narrow.

## Validation Requirements

`OTB-0-A` should fail closed when:

- source phase is absent from the catalog;
- target phase is absent from the catalog;
- transition row is absent or does not point to the bridge contract;
- transition claim is absent;
- transition claim does not match the bridge transition;
- transition claim asks for an unsupported target posture;
- catalog id/version/hash are missing or mismatched;
- bridge contract id/hash is missing or mismatched;
- required object is absent;
- required artifact file hash does not match;
- canonical payload hash does not match;
- semantic object hash does not match;
- evidence boundary hash does not match;
- obligation set hash does not match;
- object identity check is missing;
- artifact source phase does not match the required source phase;
- artifact authority layer is lower than the bridge permits;
- stale-object check fails;
- required evidence is absent;
- forbidden evidence is present;
- forbidden evidence appears in `derived_from_evidence_refs` ancestry;
- evidence boundary posture is missing or illegal;
- clean-first-pass posture is overclaimed;
- obligation required for preservation disappears;
- obligation is discharged without a discharge reference;
- obligation is deferred without a deferral reference and risk posture;
- claimed next phase is not in `next_allowed_phases`;
- promotion claim is listed in `forbidden_promotions`;
- posture downgrade is required but not represented in the frontier;
- unknown vocabulary appears in any row;
- canonical output hash is unstable.

## Legal Frontier Requirements

Blocked or invalid transitions should emit deterministic frontier rows for:

- missing object;
- stale artifact;
- forbidden evidence;
- missing warrant;
- evidence boundary violation;
- silent obligation drop;
- missing discharge or deferral proof;
- illegal promotion;
- posture downgrade required;
- target phase not allowed;
- unresolved equivalence check;
- conflict-isolated transition.

Frontier rows are not execution authority. Each row should state:

```text
authority_posture: broker_validation_only_not_execution_authority
```

or an equivalent enum.

## Non-Authority Guardrails

The first slice should explicitly state that it has no authority to:

- judge semantic truth;
- decide phase content quality;
- run probes or commands;
- dispatch workers;
- produce implementation taskpacks;
- patch code;
- grant product or official-eval readiness;
- select future families.

## Starter Acceptance Tests

Recommended first-slice tests:

```text
Test 1: valid transition
  typed transition claim present, required O/E/D/U rows present, no forbidden
  evidence, target phase allowed, and output says valid_for_broker_frontier.

Test 2: missing required object
  validation fails closed and frontier asks for object production.

Test 3: forbidden evidence contamination
  direct forbidden evidence validation fails closed and diagnostic points to
  E_bridge.

Test 4: transitive evidence contamination
  forbidden evidence in derived_from_evidence_refs ancestry fails closed.

Test 5: silent obligation drop
  validation fails closed and diagnostic points to D_bridge.

Test 6: illegal promotion
  scoped or pressure-only artifact cannot enter official-ready target phase.

Test 7: posture downgrade
  unsupported requested posture emits posture_downgrade_required frontier.

Test 8: stale artifact
  file, canonical payload, semantic object, evidence boundary, or obligation
  set hash mismatch produces stale-object frontier.

Test 9: bridge consistency versus completeness
  well-formed but incomplete bridge is not promoted as complete.

Test 10: unknown vocabulary
  validation fails closed.

Test 11: shuffled input stability
  canonical output hash is stable for semantically equivalent inputs.

Test 12: non-authority guardrail
  guardrail row denies semantic, worker-dispatch, execution, implementation,
  product, and future-family authority.
```

## Deferred To Later Slices

Deferred to `OTB-0-B`:

- aggregate transition closure summaries;
- gate execution plans;
- worker baton contracts;
- evidence posture plans;
- operationalization reports.

Deferred to `OTB-0-C`:

- transition delta attribution;
- stale object invalidation across completed runs;
- integration handoff;
- family closeout alignment.
