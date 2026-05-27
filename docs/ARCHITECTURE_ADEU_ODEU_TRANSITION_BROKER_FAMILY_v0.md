# Architecture ADEU ODEU Transition Broker Family v0

Status: architecture / decomposition note for planned `OTB-0`.

Authority layer: architecture / decomposition.

This note does not authorize semantic adjudication, ontology generation,
phase-transition runtime, probe execution, command execution, code edits,
worker dispatch, implementation authority, product authority, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself. It defines the intended family boundary so
starter locks can select bounded implementation slices.

## Family Thesis

`OTB-0` should make phase-transition legality reviewable and deterministic.

Existing families and workers can produce useful artifacts inside phases. The
missing institutional layer is the bridge between phases:

```text
phase output exists
  !=
next phase is legal
```

The broker validates the transition record:

```text
O: objects carried, compared, transformed, or preserved
E: evidence required, forbidden, scoped, or downgraded
D: obligations created, preserved, discharged, blocked, or deferred
U: use, purpose, next allowed phases, forbidden promotions, and failure routes
```

Controlling invariant:

```text
No reconstruction result, phase artifact, evidence record, or readiness claim
may transfer across a phase boundary unless the relevant O/E/D/U bridge has
been named, scoped, and witnessed.
```

## Relation To HOB

`HOB-0` and `OTB-0` are adjacent but distinct.

```text
HOB-0:
  deterministic obligation inheritance inside ontology trees

OTB-0:
  deterministic transition legality between meta-program phases
```

HOB records may become objects consumed by an OTB bridge. OTB does not
recompute HOB subtree closure and does not decide whether a HOB node applies.
It validates whether a phase transition that uses HOB records is allowed to
carry those records forward, promote their posture, or require additional
frontier work.

## Source Stack Consumed

`OTB-0` consumes:

- HOB family closeout doctrine, especially the distinction between internal
  ontology traversal and downstream handoff;
- support-layer ProgramBench methodology updates on control-schema
  reachability, official-eval posture, pre-eval saturation, and transition
  gates;
- methodological equivalence doctrine that evidence transfers only through
  witnessed equivalence;
- semantic compiler architecture doctrine on stable IDs, canonical hashes, and
  fail-closed validation.

No consumed source becomes semantic truth authority, runtime authority, product
authority, or future-family selection by being consumed.

## Family Slices

### `OTB-0-A`: Phase Catalog, Bridge Contract, And Transition Validation

Starter surfaces:

- `repo_phase_circuit_catalog@1`
- `repo_phase_bridge_contract@1`
- `repo_phase_transition_claim@1`
- `repo_phase_transition_validation_report@1`
- `repo_phase_legal_frontier_report@1`
- `repo_transition_broker_non_authority_guardrail@1`

Purpose:

- make a phase-circuit catalog row-shaped and deterministic;
- represent O/E/D/U bridge contracts between source and target phases;
- represent typed transition claims instead of inferring transition intent from
  loose artifact presence;
- validate artifact identity, hash, source phase, authority layer, and
  freshness;
- validate required and forbidden evidence conditions;
- validate obligation transfer, preservation, discharge, and deferral rows;
- reject illegal readiness, evidence, or authority promotion;
- emit deterministic legal-frontier rows and non-authority guardrails.

Slice boundary:

```text
OTB-0-A validates transition admissibility and emits blockers/frontiers.
OTB-0-B computes aggregate transition closure/readiness and operational plans.
```

Forbidden:

- full circuit closure aggregation;
- worker baton generation;
- probe-matrix generation;
- implementation batch contracts;
- code edits;
- command execution;
- product claims;
- semantic adjudication by the tool;
- future-family selection.

### `OTB-0-B`: Closure, Gate Planning, And Baton Contracts

Later surfaces:

- `repo_phase_transition_closure_report@1`
- `repo_phase_gate_execution_plan@1`
- `repo_phase_worker_baton_contract@1`
- `repo_phase_evidence_posture_plan@1`
- `repo_phase_operationalization_report@1`

Purpose:

- compute transition closure posture from released `OTB-0-A` validation
  records;
- derive the next legal phase frontier across a circuit;
- emit plan-only gate execution rows;
- emit worker baton contracts that state what a worker may consume, produce,
  and must not use;
- represent evidence posture needed before local parity, packaged preflight,
  official-like evaluation, or official evaluation;
- distinguish representative, scoped-ready, gold-ready, official-ready, and
  pressure-only transition postures.

Forbidden:

- executing gates;
- running probes, reference programs, or candidate programs;
- dispatching workers;
- patching code;
- treating a gate plan as observed evidence;
- granting implementation or product authority by itself.

### `OTB-0-C`: Delta Attribution, Stale Object Invalidation, And Closeout

Later surfaces:

- `repo_phase_transition_delta_attribution_ledger@1`
- `repo_phase_stale_object_invalidation_report@1`
- `repo_transition_broker_integration_handoff@1`
- `repo_transition_broker_family_closeout_alignment@1`

Purpose:

- attribute post-run pressure to transition bridge fields when supplied with
  admissible delta rows;
- distinguish product-theory failures from earlier transition failures;
- invalidate stale phase artifacts when upstream objects, evidence, catalogs,
  or obligation sets change;
- record when score movement is only pressure, not bridge proof;
- provide pressure-only handoffs to future HOB, semantic compiler,
  ProgramBench, or orchestration integration work;
- close only the broker family.

Forbidden:

- claiming product truth;
- treating official failures as clean first-pass evidence;
- authorizing implementation, execution, or product state changes;
- selecting future families.

## Core Data Concepts

### Phase Circuit Catalog

A phase catalog defines stable phases and legal candidate transitions:

```yaml
circuit_id: "program_reconstruction_v46"
circuit_version: "0.1.0"
circuit_hash: "sha256:..."
circuit_authority: support | architecture | lock
phase_rows:
  - phase_id: "blind_task_native_ontology"
    phase_label: "Blind task-native ontology pass"
    phase_kind: semantic_descent | reconciliation | hob_import |
      scout | probe_planning | implementation | local_parity |
      packaged_preflight | official_eval | post_eval_audit
    allowed_input_object_kinds: []
    allowed_output_object_kinds: []
    forbidden_evidence_kinds: []
transition_rows:
  - transition_id: "T03"
    from_phase: "blind_utility_descent"
    to_phase: "utility_program_reconciliation"
    bridge_contract_ref: "BRIDGE-T03"
```

The family should use one shared vocabulary source across A/B/C for:

```text
phase_kind
object_kind
artifact_authority_layer
evidence_kind
evidence_boundary_posture
obligation_transfer_status
readiness_posture
transition_validation_status
bridge_consistency_status
bridge_completeness_status
frontier_reason
promotion_kind
authority_posture
```

### Bridge Contract

A bridge contract describes what must be true for a transition:

```yaml
bridge_contract_ref: "BRIDGE-T03"
transition_id: "T03"
from_phase: "blind_utility_descent"
to_phase: "utility_program_reconciliation"

O_bridge:
  required_objects: []
  object_identity_checks: []
  transformation_claims: []
  stale_object_checks: []

E_bridge:
  required_evidence: []
  forbidden_evidence: []
  evidence_boundary_rules: []
  warrant_requirements: []

D_bridge:
  obligations_created: []
  obligations_preserved: []
  obligations_discharged: []
  obligations_blocked_or_deferred: []
  forbidden_silent_drops: true

U_bridge:
  purpose: []
  next_allowed_phases: []
  forbidden_promotions: []
  failure_routes: []
```

The broker validates the row shape and vocabulary. It does not decide semantic
truth inside the source or target phase.

### Transition Claim

A transition claim is the typed object that asks the broker to validate a
specific movement between phases:

```yaml
transition_claim_ref: "CLAIM-T03-001"
claiming_actor_ref: "orchestrator:..."
claim_source: orchestrator | worker_closeout | planner | broker_output |
  manual_review
circuit_id: "program_reconstruction_v46"
circuit_version: "0.1.0"
circuit_hash: "sha256:..."
from_phase: "blind_utility_descent"
to_phase: "utility_program_reconciliation"
transition_id: "T03"
claimed_transition_kind: "reconciliation_input"
claimed_readiness_posture: "scoped_ready"
claimed_evidence_posture: "clean_visible_packet_only"
claimed_promotion: null
artifact_refs: []
evidence_refs: []
obligation_transfer_refs: []
intended_use: "map utility obligations into program ontology"
requested_next_frontier: null
claim_hash: "sha256:..."
```

The broker validates claims. It should not infer a claim merely because an
artifact exists.

### Phase Artifact Row

Phase artifacts are objects carried through a bridge:

```yaml
artifact_ref: "artifact://..."
artifact_kind: "utility_obligation_set"
source_phase: "blind_utility_descent"
authority_layer: support | architecture | planning | lock | observed |
  post_eval_pressure
file_hash: "sha256:..."
canonical_payload_hash: "sha256:..."
semantic_object_hash: "sha256:..."
catalog_hash: "sha256:..."
bridge_hash: "sha256:..."
evidence_boundary_hash: "sha256:..."
obligation_set_hash: "sha256:..."
object_identity_claim: "same_visible_packet"
evidence_refs: []
freshness_basis: []
```

Artifact rows should be fresh against the catalog and bridge hashes that consume
them.

### Evidence Row

Evidence rows carry explicit ancestry so contamination can be checked
transitively:

```yaml
evidence_ref: "EVID-..."
evidence_kind: "visible_spec"
source_phase: "blind_task_native_ontology"
authority_layer: support | observed | post_eval_pressure
boundary_posture: "clean_first_pass_allowed"
clean_first_pass_posture: "clean"
evidence_hash: "sha256:..."
derived_from_evidence_refs: []
contamination_tags: []
```

Validation rule:

```text
If forbidden evidence appears anywhere in the ancestry of a transition input,
the transition is contaminated unless the bridge explicitly permits that
posture and downgrades the use.
```

### Transition Validation Report

A validation report records transition admissibility:

```yaml
transition_validation_report_ref: "OTB-A-..."
circuit_id: "program_reconstruction_v46"
circuit_version: "0.1.0"
circuit_hash: "sha256:..."
transition_id: "T03"
bridge_contract_ref: "BRIDGE-T03"
validation_status: valid_for_broker_frontier | blocked | invalid | stale |
  conflict_isolated
bridge_consistency_status: consistent | inconsistent | unknown_vocabulary |
  hash_mismatch
bridge_completeness_status: complete | missing_required_object |
  missing_required_evidence | missing_obligation_transfer |
  missing_equivalence | missing_warrant | missing_deferral_risk
diagnostic_rows: []
legal_frontier_rows: []
canonical_output_hash: "sha256:..."
```

`valid_for_broker_frontier` is not action authority. It only means the bridge is
structurally admissible enough for the broker to name the legal frontier.

### Legal Frontier Row

Frontier rows state what must happen before the transition can proceed:

```yaml
frontier_ref: "FRONTIER-T03-001"
transition_id: "T03"
frontier_reason: missing_object | forbidden_evidence | stale_artifact |
  silent_obligation_drop | illegal_promotion | blocked_equivalence |
  missing_warrant | conflict_isolated | posture_downgrade_required
required_next_action: produce_object | remove_forbidden_evidence |
  refresh_artifact | discharge_or_defer_obligation | downgrade_promotion |
  run_equivalence_preflight | route_to_human_review
authority_posture: broker_validation_only_not_execution_authority
requested_posture: "official_ready_candidate"
maximum_supported_posture: "scoped_method_test_only"
downgrade_basis: []
required_revalidation_frontier: []
```

## Non-Authority Boundary

`OTB-0` is a deterministic transition validator and planner. It must not become:

- a semantic judge;
- a domain ontology generator;
- a HOB closure engine;
- a probe generator;
- a probe runner;
- a command executor;
- a worker dispatcher;
- an implementation planner in `OTB-0-A`;
- a product authority;
- an official-eval authority;
- a future-family selector.

## Validation Philosophy

`OTB-0` should fail closed when:

- required objects are absent;
- object hashes, catalog hashes, or bridge hashes mismatch;
- evidence-boundary or obligation-set hashes mismatch;
- forbidden evidence appears in a target phase;
- forbidden evidence appears in ancestry without an explicit downgrade rule;
- evidence boundary posture is missing or illegal;
- obligations are dropped without discharge, deferral, blocker, or explicit
  pass-through;
- scoped, representative, pressure-only, or post-eval evidence is promoted
  beyond its authority layer;
- next phase is not listed in the bridge contract;
- transition claims depend on stale phase artifacts;
- transition claims request stronger posture than the bridge can support;
- circuit rows use unknown vocabulary;
- canonical hash stability is broken.

## Example Transition

```yaml
transition_id: "T03"
from_phase: "blind_utility_descent"
to_phase: "utility_program_reconciliation"

O_bridge:
  required_objects:
    - "utility_obligation_set"
    - "program_ontology_tree"
  object_identity_checks:
    - "same_visible_packet"
    - "utility_branch_blind_to_program_branch"

E_bridge:
  required_evidence:
    - "utility_output_exists"
    - "program_ontology_output_exists"
  forbidden_evidence:
    - "official_failures"
    - "implementation_notes"
    - "source_tail"

D_bridge:
  obligations_created:
    - "every_utility_obligation_maps_creates_candidate_defers_or_blocks"
  forbidden_silent_drops: true

U_bridge:
  purpose:
    - "enrich_program_ontology_with_user_job_pressure"
  next_allowed_phases:
    - "merged_activation"
  forbidden_promotions:
    - "utility_obligation_direct_to_implementation_task"
```

## Success Criteria

The family succeeds if it makes the following move mechanically reviewable:

```text
phase artifact present
  -> bridge conditions checked
  -> illegal transition blocked
  -> legal next frontier emitted
```

It should reduce the class of failures where a run skips adversarial passes,
promotes scoped artifacts to official posture, carries stale objects forward,
or begins implementation before evidence/object/obligation/use bridges have
been satisfied.
