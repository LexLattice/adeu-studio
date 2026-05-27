# Draft ADEU ODEU Transition Broker OTB-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `OTB-0-B`.

Authority layer: support.

This note maps likely implementation for `OTB-0-B`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment. `OTB-0-B` should remain deferred until
`OTB-0-A` has been released and real A artifacts exist.

## Slice Intent

`OTB-0-B` should consume released `OTB-0-A` records and compute transition
closure posture, gate plans, worker baton contracts, and evidence posture plans.

It should answer:

```text
Given validated transition records and legal-frontier reports, what phase
frontier is closed, blocked, scoped, or ready for a bounded next-phase baton?
```

It must not answer:

```text
Did the worker actually run?
Did a probe pass?
Should code be patched?
Did the product behavior become correct?
Did the official score improve?
```

## Selected Surfaces

Likely schema / model surfaces:

- `repo_phase_transition_closure_report@1`
- `repo_phase_gate_execution_plan@1`
- `repo_phase_worker_baton_contract@1`
- `repo_phase_evidence_posture_plan@1`
- `repo_phase_operationalization_report@1`

Likely source files:

- `packages/adeu_transition_broker/src/adeu_transition_broker/closure.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/gates.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/baton.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/evidence_posture.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/operationalization.py`
- `packages/adeu_transition_broker/tests/test_otb_0b.py`

## Field-Level Expectations

`repo_phase_transition_closure_report@1` should include:

- `transition_closure_report_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `input_validation_report_refs`
- `closure_rows`
- `frontier_summary_rows`
- `canonical_output_hash`

Closure rows should include:

- `transition_id`
- `from_phase`
- `to_phase`
- `closure_status`
- `readiness_posture`
- `closure_basis`
- `blocking_frontier_refs`
- `allowed_next_phase_refs`

Allowed `closure_basis` values should include:

- `all_required_bridges_valid`
- `blocked_by_A_validation`
- `blocked_by_frontier`
- `scoped_ready_with_known_risk`
- `representative_only`
- `deferred_with_risk`
- `conflict_isolated`

`repo_phase_gate_execution_plan@1` should include:

- `gate_execution_plan_ref`
- `transition_closure_report_ref`
- `gate_plan_rows`
- `plan_authority_posture`

Gate plan rows should include:

- `gate_ref`
- `transition_id`
- `gate_kind`
- `required_input_refs`
- `expected_output_kinds`
- `forbidden_evidence_kinds`
- `success_posture`
- `failure_route`

Every gate plan row should have:

```text
plan_authority_posture: plan_only_not_execution_authority
```

or an equivalent enum.

`repo_phase_worker_baton_contract@1` should include:

- `worker_baton_contract_ref`
- `transition_id`
- `source_phase_refs`
- `target_phase`
- `allowed_inputs`
- `required_outputs`
- `forbidden_inputs`
- `forbidden_promotions`
- `required_closeout_rows`
- `baton_authority_posture`

Every baton contract row should carry a non-dispatch posture:

```text
baton_authority_posture: baton_contract_only_not_dispatch_authority
```

`OTB-0-B` may say:

```text
if an external authority chooses to dispatch, this is the maximum bounded
baton contract consistent with the validated transition.
```

It may not say:

```text
worker may run
```

`repo_phase_evidence_posture_plan@1` should include:

- `evidence_posture_plan_ref`
- `transition_id`
- `current_evidence_posture`
- `target_evidence_posture`
- `required_equivalence_checks`
- `forbidden_evidence_leaks`
- `official_readiness_requirements`

`repo_phase_operationalization_report@1` should include:

- `operationalization_report_ref`
- `transition_closure_report_ref`
- `recommended_next_frontier`
- `blocked_frontier`
- `deferred_frontier`
- `handoff_constraints`

## Core API Expectations

The implementation should expose deterministic module APIs equivalent to:

```text
compute_transition_closure(catalog, validation_reports)
  -> PhaseTransitionClosureReport
plan_transition_gates(closure_report) -> PhaseGateExecutionPlan
build_worker_baton_contract(closure_report, target_phase)
  -> PhaseWorkerBatonContract
plan_evidence_posture(closure_report, target_phase)
  -> PhaseEvidencePosturePlan
emit_operationalization_report(closure_report, gate_plan, baton, evidence_plan)
  -> PhaseOperationalizationReport
canonical_hash(payload) -> sha256
```

Names may vary if repo conventions prefer different names.

## Validation Requirements

`OTB-0-B` should fail closed when:

- consumed `OTB-0-A` validation report has blocking diagnostics;
- consumed report hash does not match the closure input row;
- closure posture exceeds the weakest required transition;
- representative-only transition is marked gold-ready or official-ready;
- scoped-ready transition lacks known-risk statement;
- gate plan row implies execution authority;
- worker baton includes inputs forbidden by the bridge;
- worker baton asks for outputs outside the target phase;
- evidence posture plan omits required equivalence checks;
- official-eval posture is claimed before packaged/equivalence preflight is
  represented;
- unknown vocabulary appears in any row.

## Non-Authority Guardrails

`OTB-0-B` can plan and summarize. It cannot:

- execute gates;
- run probes;
- dispatch workers;
- patch code;
- judge product behavior;
- grant official-eval authority;
- treat a plan as observed evidence.

## Deferred To Later Slice

Deferred to `OTB-0-C`:

- attributing actual run deltas to bridge fields;
- invalidating stale artifacts after an observed run;
- producing integration handoff records;
- family closeout alignment.
