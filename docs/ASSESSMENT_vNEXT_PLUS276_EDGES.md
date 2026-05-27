# Assessment vNext+276 Edges

Status: pre-lock edge assessment for `OTB-0-B`.

Authority layer: planning assessment.

This document records pre-implementation edge analysis for `vNext+276`
(`OTB-0-B` transition closure, gate execution plan, worker baton contract,
evidence posture plan, and operationalization report), aligned to
`docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS276_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Scope

In scope:

- closure/readiness summaries over released A validation reports;
- frontier summaries from A legal frontier rows;
- plan-only gate execution records;
- non-dispatch worker baton contracts;
- evidence posture plans;
- non-executing operationalization reports;
- canonical hashing and schema export for B surfaces.

Out of scope:

- semantic adjudication;
- domain ontology generation;
- HOB closure recomputation;
- gate execution;
- probe generation or execution;
- worker dispatch;
- product behavior claims;
- official-eval authority;
- transition delta attribution;
- stale-object invalidation after observed runs;
- integration handoff;
- family closeout alignment;
- future-family selection.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
- `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS275.md`
- `docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md`
- `artifacts/agent_harness/v275/evidence_inputs/otb_0a_closeout_evidence_v275.json`

## Edge Set

### Edge 1: Plan Closure Reopens A Validation

- Risk:
  B recomputes A transition validity instead of consuming released A reports.
- Guardrail:
  B consumes A validation reports and legal-frontier rows; it does not reopen
  A bridge validation.

### Edge 2: Closure Posture Exceeds Weakest Transition

- Risk:
  one valid transition row promotes a mixed frontier to gold or official
  readiness.
- Guardrail:
  closure posture is bounded by the weakest required transition and explicit
  closure basis.

### Edge 3: Representative Coverage Becomes Gold Readiness

- Risk:
  representative-only rows are marked gold-ready or official-ready.
- Guardrail:
  representative-only rows cannot promote beyond representative posture.

### Edge 4: Scoped Readiness Hides Known Risk

- Risk:
  scoped-ready closure is emitted without naming the scoped risk.
- Guardrail:
  scoped-ready rows require known-risk refs.

### Edge 5: Gate Plan Becomes Gate Execution

- Risk:
  gate execution plan rows are interpreted as permission to run gates.
- Guardrail:
  every gate row carries `plan_only_not_execution_authority`.

### Edge 6: Worker Baton Becomes Worker Dispatch

- Risk:
  baton contracts are treated as taskpacks or dispatch authority.
- Guardrail:
  baton rows carry `baton_contract_only_not_dispatch_authority` and only define
  maximum legal inputs/outputs if an external authority later dispatches.

### Edge 7: Evidence Posture Plan Becomes Observed Evidence

- Risk:
  planned equivalence checks are treated as evidence already gathered.
- Guardrail:
  evidence posture plans distinguish planned evidence from observed evidence
  and require equivalence checks before official-ready posture.

### Edge 8: Operationalization Report Becomes Implementation Authority

- Risk:
  recommended next frontier is treated as authorization to patch code or run
  commands.
- Guardrail:
  operationalization reports remain non-executing and non-authoritative.

### Edge 9: C Surfaces Leak Into B

- Risk:
  B emits delta attribution, stale-object invalidation, integration handoff, or
  family closeout records.
- Guardrail:
  B emits closure, gate, baton, evidence posture, and operationalization records
  only.

### Edge 10: Canonical Determinism Is Claimed But Not Tested

- Risk:
  closure/gate/baton rows reorder under shuffled inputs.
- Guardrail:
  shuffled input fixture must preserve canonical output order and hash.

## Required Guardrails

- Released-A substrate lock:
  - B consumes released A validation and frontier reports.
- Weakest-posture lock:
  - closure posture cannot exceed weakest required transition.
- Plan-only lock:
  - gate plans, baton contracts, evidence posture plans, and
    operationalization reports do not authorize execution.
- Representative/scoped lock:
  - representative and scoped postures require explicit downgrade/risk
    handling.
- Boundary lock:
  - no C-level delta, stale, handoff, or family-closeout outputs in B.

## Acceptance Evidence Targets

- Five B-level record shapes are modeled and schema-exported.
- Focused tests cover the required starter fixtures in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS276.md`.
- Canonical hashing is stable under shuffled inputs.
- B consumes A validation reports and rejects blocked/stale A substrate where
  closure requires validity.
- No gate execution, probe execution, worker dispatch, implementation authority,
  product authority, official-eval authority, or C-level integration handoff APIs
  are present in B.

## Implementation Readiness Notes

1. `OTB-0-B` is implementation-ready as a bounded deterministic planning slice
   after starter-bundle acceptance.
2. Highest risks are overpromotion from plan to action authority and treating
   representative/scoped readiness as gold readiness.
3. Recommended implementation order:
   - shared B vocabulary and canonical hashing;
   - closure report models/builders;
   - gate plan and baton contract models/builders;
   - evidence posture and operationalization report models/builders;
   - schema export and focused fixtures.
