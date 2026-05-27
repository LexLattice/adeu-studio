# LOCKED_CONTINUATION_vNEXT_PLUS276

## Status

Bounded starter lock draft for `OTB-0-B` (transition closure report, gate
execution plan, worker baton contract, evidence posture plan, and
operationalization report).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`OTB-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `OTB-0`
- slice: `OTB-0-B`
- branch-local execution target: `arc/otb-0-b`

## Purpose

Freeze the bounded `OTB-0-B` starter slice so the repo can consume released
`OTB-0-A` validation reports and compute transition closure, next legal
frontier planning, gate plans, worker baton contracts, evidence posture plans,
and operationalization reports without turning plans into execution authority.

`vNext+276` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_transition_broker` package. It does not authorize semantic
adjudication, domain ontology generation, HOB closure recomputation, gate
execution, probe generation, probe execution, command execution outside the
implementation/test lane, worker dispatch, implementation batches, product
authorization, official-eval submission, graph-memory authority, future-family
selection, release authority, or recursive policy amendment.

Controlling invariant:

```text
OTB-0-B may compute closure and plan-only operational records from released
OTB-0-A validation reports.

OTB-0-B may not execute the plans it emits, dispatch a worker, run a probe,
patch code, claim product correctness, or grant official readiness.
```

## Instantiated Here

- `OTB-0-B` instantiates the second deterministic transition-broker seam:
  - existing repo-owned package:
    - `adeu_transition_broker`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
    - `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS275.md`
    - `docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md`
    - `artifacts/agent_harness/v275/evidence_inputs/otb_0a_closeout_evidence_v275.json`
  - consumed package surfaces:
    - `packages/adeu_transition_broker/src/adeu_transition_broker/otb_0a.py`
    - `packages/adeu_transition_broker/tests/test_otb_0a.py`
    - `packages/adeu_transition_broker/schema/`
  - emitted starter record shapes:
    - `repo_phase_transition_closure_report@1`
    - `repo_phase_gate_execution_plan@1`
    - `repo_phase_worker_baton_contract@1`
    - `repo_phase_evidence_posture_plan@1`
    - `repo_phase_operationalization_report@1`

## Required Starter Vocabulary

`OTB-0-B` must reuse the A vocabulary where possible and add only B-level
planning vocabulary:

- `transition_closure_status`
- `closure_basis`
- `gate_kind`
- `gate_plan_authority_posture`
- `baton_authority_posture`
- `evidence_posture_plan_authority`
- `operationalization_authority_posture`

Required closure statuses:

```text
closed
blocked
scoped_ready
representative_only
deferred
conflict_isolated
```

Required closure bases:

```text
all_required_bridges_valid
blocked_by_A_validation
blocked_by_frontier
scoped_ready_with_known_risk
representative_only
deferred_with_risk
conflict_isolated
```

## Required Record Shapes

Minimum `repo_phase_transition_closure_report@1` fields:

- `transition_closure_report_ref`
- `circuit_id`
- `circuit_version`
- `circuit_hash`
- `input_validation_report_refs`
- `closure_rows`
- `frontier_summary_rows`
- `canonical_output_hash`

Closure rows must include:

- `transition_id`
- `from_phase`
- `to_phase`
- `closure_status`
- `readiness_posture`
- `closure_basis`
- `blocking_frontier_refs`
- `allowed_next_phase_refs`
- `known_risk_ref`

Minimum `repo_phase_gate_execution_plan@1` fields:

- `gate_execution_plan_ref`
- `transition_closure_report_ref`
- `gate_plan_rows`
- `plan_authority_posture`
- `canonical_output_hash`

Every gate plan row must carry:

```text
plan_authority_posture: plan_only_not_execution_authority
```

Minimum `repo_phase_worker_baton_contract@1` fields:

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
- `canonical_output_hash`

Every baton row must carry:

```text
baton_authority_posture: baton_contract_only_not_dispatch_authority
```

Minimum `repo_phase_evidence_posture_plan@1` fields:

- `evidence_posture_plan_ref`
- `transition_id`
- `current_evidence_posture`
- `target_evidence_posture`
- `required_equivalence_checks`
- `forbidden_evidence_leaks`
- `official_readiness_requirements`
- `plan_authority_posture`
- `canonical_output_hash`

Minimum `repo_phase_operationalization_report@1` fields:

- `operationalization_report_ref`
- `transition_closure_report_ref`
- `recommended_next_frontier`
- `blocked_frontier`
- `deferred_frontier`
- `handoff_constraints`
- `operationalization_authority_posture`
- `canonical_output_hash`

## Required APIs

`OTB-0-B` must provide deterministic functions or equivalent module APIs that:

- load released `OTB-0-A` catalog, bridge, validation, and legal frontier
  records;
- reject validation reports with blocking diagnostics when closure requires a
  valid transition;
- compute transition closure posture without exceeding the weakest required
  transition posture;
- emit plan-only gate execution rows;
- emit worker baton contracts that deny dispatch authority;
- emit evidence posture plans that distinguish planned evidence from observed
  evidence;
- emit operationalization reports that summarize the next legal frontier without
  executing it;
- compute stable canonical hashes independent of input order.

## Required Validation

`OTB-0-B` must fail closed when:

- consumed `OTB-0-A` validation report has blocking diagnostics;
- consumed report hash does not match the closure input row;
- closure posture exceeds the weakest required transition;
- representative-only transition is marked gold-ready or official-ready;
- scoped-ready transition lacks a known-risk statement;
- gate plan row implies execution authority;
- worker baton contract implies dispatch authority;
- worker baton includes inputs forbidden by the bridge or A frontier;
- worker baton asks for outputs outside the target phase;
- evidence posture plan omits required equivalence checks;
- official-eval posture is claimed before packaged/equivalence preflight is
  represented;
- operationalization report implies product, execution, implementation, worker
  dispatch, or official-eval authority;
- unknown vocabulary appears in any row.

## Required Starter Fixtures

`OTB-0-B` must include focused fixtures for:

1. all required A reports valid produces closed/scoped closure rows;
2. blocking A validation report blocks closure;
3. closure posture cannot exceed weakest required transition;
4. representative-only cannot be promoted to gold or official readiness;
5. scoped-ready row without known-risk ref fails closed;
6. gate plan row with execution authority fails closed;
7. worker baton row with dispatch authority fails closed;
8. worker baton forbidden input fails closed;
9. evidence posture plan without equivalence checks fails closed;
10. operationalization report remains non-executing and non-authoritative;
11. shuffled input order preserves output order and canonical hashes.

## Deferred

Deferred to `OTB-0-C`:

- attributing actual run deltas to transition bridge fields;
- invalidating stale phase objects after observed runs;
- producing integration handoff records;
- family closeout alignment.

Deferred to later families:

- actually running generated gates or probes;
- dispatching workers;
- patching product code;
- ProgramBench integration;
- semantic compiler integration;
- implementation authority;
- official-result governance.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+276",
  "target_path": "OTB-0-B",
  "authority_layer": "lock",
  "selected_family": "OTB-0",
  "selected_slice": "OTB-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS276.md",
  "allowed_package": "packages/adeu_transition_broker",
  "selected_record_shapes": [
    "repo_phase_transition_closure_report@1",
    "repo_phase_gate_execution_plan@1",
    "repo_phase_worker_baton_contract@1",
    "repo_phase_evidence_posture_plan@1",
    "repo_phase_operationalization_report@1"
  ],
  "local_gate": "make arc-start-check ARC=276",
  "non_authority_summary": "No semantic adjudication, gate execution, probe execution, worker dispatch, product truth, implementation authority, official-eval authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=276
```

Before opening the implementation PR:

```text
make check
```
