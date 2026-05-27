# LOCKED_CONTINUATION_vNEXT_PLUS275

## Status

Bounded starter lock draft for `OTB-0-A` (phase circuit catalog, O/E/D/U bridge
contract, transition claim, transition validation report, legal-frontier report,
and non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`OTB-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `OTB-0`
- slice: `OTB-0-A`
- branch-local execution target: `arc/otb-0-a`

## Purpose

Freeze the bounded `OTB-0-A` starter slice so the repo can validate
phase-transition legality across the ODEU meta-program circuit without turning
the transition broker into a semantic judge, domain ontology author, HOB closure
engine, probe executor, implementation planner, worker dispatcher, product
authority, official-eval authority, or future-family selector.

`vNext+275` authorizes docs plus the next implementation path over a new
repo-owned transition-broker package. It does not authorize semantic
adjudication, ontology generation, HOB closure recomputation, probe generation,
probe execution, command execution outside the implementation/test lane, worker
dispatch, implementation batches, code patches outside the slice package,
runtime transition, product authorization, official-eval submission,
graph-memory authority, future-family selection, release authority, or recursive
policy amendment.

Controlling invariant:

```text
Phase artifacts do not make a next phase legal by existing.

The broker may validate a typed transition claim against a fixed phase circuit,
O/E/D/U bridge contract, artifact rows, evidence rows, and obligation-transfer
rows.

The broker may emit validation diagnostics and legal-frontier rows.

The broker may not decide semantic truth, authorize execution, dispatch a
worker, or promote the target phase to product or official readiness.
```

## Instantiated Here

- `OTB-0-A` instantiates the first deterministic transition-broker seam:
  - new repo-owned package:
    - `adeu_transition_broker`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
    - `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS274.md`
    - `docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md`
    - `docs/support/principled_recursive_odeu_meta_program_experimental_v46.md`
    - `docs/support/general_program_ontology_derived_v1_7.md`
  - emitted starter record shapes:
    - `repo_phase_circuit_catalog@1`
    - `repo_phase_bridge_contract@1`
    - `repo_phase_transition_claim@1`
    - `repo_phase_transition_validation_report@1`
    - `repo_phase_legal_frontier_report@1`
    - `repo_transition_broker_non_authority_guardrail@1`

## Machine-Checkable Contract

```json
{
  "schema": "otb_0a_starter_contract@1",
  "target_arc": "vNext+275",
  "target_path": "OTB-0-A",
  "family": "OTB-0",
  "slice": "OTB-0-A",
  "implementation_package": "packages/adeu_transition_broker",
  "selected_record_shapes": [
    "repo_phase_circuit_catalog@1",
    "repo_phase_bridge_contract@1",
    "repo_phase_transition_claim@1",
    "repo_phase_transition_validation_report@1",
    "repo_phase_legal_frontier_report@1",
    "repo_transition_broker_non_authority_guardrail@1"
  ],
  "semantic_authority_granted": false,
  "domain_ontology_authority_granted": false,
  "hob_closure_authority_granted": false,
  "probe_generation_authority_granted": false,
  "probe_execution_authority_granted": false,
  "implementation_authority_granted": false,
  "worker_dispatch_authority_granted": false,
  "product_authority_granted": false,
  "official_eval_authority_granted": false,
  "future_family_selection_granted": false
}
```

## Required Starter Vocabulary

The implementation must define one shared vocabulary source for A/B/C-ready
terms, even though only A surfaces ship in this slice.

Minimum shared vocabulary:

- `phase_kind`
- `object_kind`
- `artifact_authority_layer`
- `evidence_kind`
- `evidence_boundary_posture`
- `obligation_transfer_status`
- `readiness_posture`
- `transition_validation_status`
- `bridge_consistency_status`
- `bridge_completeness_status`
- `frontier_reason`
- `promotion_kind`
- `authority_posture`

Minimum `repo_phase_circuit_catalog@1` fields:

- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `circuit_authority`
- `phase_rows`
- `transition_rows`
- `allowed_status_vocabulary`
- `shared_vocabulary_ref`

Minimum phase row fields:

- `phase_id`
- `phase_label`
- `phase_kind`
- `allowed_input_object_kinds`
- `allowed_output_object_kinds`
- `forbidden_evidence_kinds`
- `authority_layer`

Minimum transition row fields:

- `transition_id`
- `from_phase`
- `to_phase`
- `bridge_contract_ref`
- `transition_kind`
- `default_failure_route`

Minimum `repo_phase_bridge_contract@1` fields:

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

Required bridge groups:

- `O_bridge`:
  - `required_objects`
  - `object_identity_checks`
  - `required_artifact_hash_checks`
  - `transformation_claims`
  - `stale_object_checks`
- `E_bridge`:
  - `required_evidence`
  - `forbidden_evidence`
  - `evidence_boundary_rules`
  - `warrant_requirements`
- `D_bridge`:
  - `obligations_created`
  - `obligations_preserved`
  - `obligations_discharged`
  - `obligations_blocked_or_deferred`
  - `forbidden_silent_drops`
- `U_bridge`:
  - `purpose`
  - `next_allowed_phases`
  - `forbidden_promotions`
  - `failure_routes`

Minimum `repo_phase_transition_claim@1` fields:

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

Required claim source values:

```text
orchestrator
worker_closeout
planner
broker_output
manual_review
```

Artifact rows consumed by A must use multi-hash identity fields:

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

Evidence rows consumed by A must include ancestry:

- `evidence_ref`
- `evidence_kind`
- `source_phase`
- `authority_layer`
- `boundary_posture`
- `clean_first_pass_posture`
- `evidence_hash`
- `derived_from_evidence_refs`
- `contamination_tags`

Obligation-transfer rows consumed by A must include:

- `obligation_ref`
- `source_phase`
- `target_phase`
- `transfer_status`
- `discharge_ref`
- `deferral_ref`
- `blocker_ref`
- `preservation_required`

Minimum `repo_phase_transition_validation_report@1` fields:

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

Required A-level `validation_status` values:

```text
valid_for_broker_frontier
blocked
invalid
stale
conflict_isolated
```

Forbidden A-level readiness outputs:

```text
ready
implementation_ready
gold_ready
official_ready
execution_authorized
```

Required `bridge_consistency_status` values:

```text
consistent
inconsistent
unknown_vocabulary
hash_mismatch
```

Required `bridge_completeness_status` values:

```text
complete
missing_required_object
missing_required_evidence
missing_obligation_transfer
missing_equivalence
missing_warrant
missing_deferral_risk
```

Minimum frontier row fields:

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

Required frontier authority posture:

```text
broker_validation_only_not_execution_authority
```

Minimum `repo_transition_broker_non_authority_guardrail@1` fields:

- `transition_broker_non_authority_guardrail_ref`
- `semantic_authority_posture`
- `domain_ontology_authority_posture`
- `hob_closure_authority_posture`
- `probe_generation_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `worker_dispatch_authority_posture`
- `product_authority_posture`
- `official_eval_authority_posture`
- `future_family_selection_posture`

## Required APIs

`OTB-0-A` must provide deterministic functions or equivalent module APIs that:

1. load and validate a phase circuit catalog;
2. load and validate an O/E/D/U bridge contract against the catalog;
3. load and validate a typed transition claim;
4. validate artifact rows, evidence rows, and obligation-transfer rows;
5. validate a claimed transition against object, evidence, obligation, and use
   bridge requirements;
6. distinguish bridge consistency from bridge completeness;
7. check direct and transitive evidence contamination;
8. check multi-hash artifact identity and phase-local freshness;
9. reject unsupported posture promotions and emit downgrade frontiers;
10. emit deterministic legal-frontier rows for blocked transitions;
11. canonicalize output order and hashes regardless of input row order;
12. emit a non-authority guardrail.

## Required Validation

`OTB-0-A` must fail closed when:

- source or target phase is absent from the catalog;
- transition row is absent or does not point to the bridge contract;
- transition claim is absent;
- transition claim does not match the bridge transition;
- transition claim asks for an unsupported target posture;
- catalog id/version/hash are missing or mismatched;
- bridge contract id/hash is missing or mismatched;
- required object is absent;
- artifact `file_hash`, `canonical_payload_hash`, `semantic_object_hash`,
  `evidence_boundary_hash`, or `obligation_set_hash` does not match;
- object identity check is missing;
- artifact source phase does not match the required source phase;
- artifact authority layer is lower than the bridge permits;
- phase-local freshness basis does not match the bridge;
- required evidence is absent;
- forbidden evidence is present directly;
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

## Required Starter Fixtures

The first implementation must include deterministic fixtures covering:

```text
1. valid transition -> valid_for_broker_frontier
2. missing required object -> fail closed and frontier asks for object
3. artifact hash mismatch -> stale-object frontier
4. direct forbidden evidence -> E_bridge diagnostic
5. transitive forbidden evidence ancestry -> E_bridge diagnostic
6. missing evidence boundary posture -> fail closed
7. clean-first-pass posture overclaim -> fail closed
8. silent obligation drop -> D_bridge diagnostic
9. discharge without discharge_ref -> fail closed
10. deferral without risk posture -> fail closed
11. target phase not allowed -> fail closed
12. forbidden promotion -> fail closed
13. unsupported requested posture -> posture_downgrade_required frontier
14. consistent but incomplete bridge -> not complete
15. unknown vocabulary -> fail closed
16. shuffled input order -> stable canonical output hash
17. legal frontier rows carry broker_validation_only_not_execution_authority
18. non-authority guardrail denies semantic/probe/implementation/product
    authority
```

## Deferred

Deferred to `OTB-0-B`:

- aggregate transition closure/readiness summaries;
- gate execution plans;
- worker baton contracts;
- evidence posture plans;
- operationalization reports;
- any baton posture stronger than
  `baton_contract_only_not_dispatch_authority`.

Deferred to `OTB-0-C`:

- transition delta attribution;
- stale phase-object invalidation after observed runs;
- integration handoff;
- family closeout alignment.

Deferred to later families or explicit future locks:

- semantic adjudication;
- domain ontology generation;
- HOB closure recomputation;
- probe generation;
- probe execution;
- worker dispatch;
- implementation taskpack authority;
- product behavior authority;
- official-eval authority;
- ProgramBench integration;
- future-family selection.

## Implementation Readiness Notes

`OTB-0-A` is implementation-ready as a bounded deterministic validation slice
after this starter bundle is accepted.

Recommended implementation order:

1. shared vocabulary and canonical hashing;
2. Pydantic or dataclass models for catalog, bridge, transition claim,
   artifacts, evidence, obligations, diagnostics, frontier, and guardrail;
3. catalog and bridge validation;
4. transition-claim validation;
5. artifact/evidence/obligation validation;
6. transition validation and legal-frontier emission;
7. schema export;
8. focused tests for all starter fixtures.

