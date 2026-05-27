# Assessment vNext+277 Edges

Status: pre-lock edge assessment for `OTB-0-C`.

Authority layer: planning assessment.

This document records pre-implementation edge analysis for `vNext+277`
(`OTB-0-C` transition delta attribution, stale object invalidation, integration
handoff, and family closeout alignment), aligned to
`docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS277_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Scope

In scope:

- pressure-only attribution from run deltas to transition bridge fields;
- stale phase-object invalidation;
- constrained integration handoff records;
- family closeout alignment records;
- canonical hashing and schema export for C surfaces.

Out of scope:

- semantic adjudication;
- clean product truth;
- implementation authority;
- gate execution;
- probe generation or execution;
- worker dispatch;
- official-eval submission;
- ProgramBench integration;
- future-family selection;
- recursive policy amendment.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v87.md`
- `docs/ARCHITECTURE_ADEU_ODEU_TRANSITION_BROKER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_ODEU_TRANSITION_BROKER_OTB_0C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS275.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS276.md`
- `docs/ASSESSMENT_vNEXT_PLUS275_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS276_EDGES.md`
- `artifacts/agent_harness/v275/evidence_inputs/otb_0a_closeout_evidence_v275.json`
- `artifacts/agent_harness/v276/evidence_inputs/otb_0b_closeout_evidence_v276.json`

## Edge Set

### Edge 1: Score Movement Becomes Bridge Proof

- Risk:
  a run delta is treated as proof that the transition bridge is correct.
- Guardrail:
  score movement is pressure only unless independent transition evidence is
  present.

### Edge 2: Post-Eval Pressure Becomes Clean First-Pass Evidence

- Risk:
  official/postmortem pressure is laundered into a clean first-pass warrant.
- Guardrail:
  every attribution row carries explicit evidence boundary posture.

### Edge 3: Downstream Product Semantics Hide Earlier Transition Failure

- Risk:
  failures are attributed to product leaves while object identity, bridge
  equivalence, evidence boundary, or substrate transitions are still unproven.
- Guardrail:
  earliest unproven or broken transition bridge dominates attribution.

### Edge 4: Stale Artifacts Are Reused

- Risk:
  changed phase objects are consumed without invalidation or revalidation.
- Guardrail:
  object hash, catalog hash, bridge contract hash, evidence boundary,
  obligation set, target substrate, and run topology changes emit invalidation.

### Edge 5: Handoff Grants Authority

- Risk:
  integration handoff records become implementation, execution, product, or
  future-family authority.
- Guardrail:
  handoff rows enumerate allowed and forbidden consumption and deny authority
  outside the C contract.

### Edge 6: Family Closeout Overclaims Completion

- Risk:
  closeout alignment marks a surface complete without accepted surface rows.
- Guardrail:
  completed slices require accepted surface rows; deferred surfaces remain
  explicit.

### Edge 7: C Reopens A/B Instead Of Consuming Them

- Risk:
  C recomputes A validation or B closure instead of consuming released records.
- Guardrail:
  C accepts A/B substrate as inputs and attributes pressure/invalidation around
  those records.

### Edge 8: Canonical Determinism Is Claimed But Not Tested

- Risk:
  attribution, invalidation, handoff, or closeout rows reorder under shuffled
  inputs.
- Guardrail:
  shuffled input fixture must preserve canonical output order and hash.

## Required Guardrails

- Pressure-only lock:
  - deltas create attribution pressure, not clean truth.
- Evidence-boundary lock:
  - every attribution row states allowed evidence posture.
- Dominance lock:
  - earliest unproven transition bridge dominates downstream attribution.
- Stale-object lock:
  - changed bridge/object/evidence/substrate/topology records require
    invalidation and revalidation frontier.
- Handoff lock:
  - integration handoff constrains downstream use but does not grant action
    authority.
- Closeout lock:
  - family closeout alignment cannot silently complete deferred or unaccepted
    surfaces.

## Acceptance Evidence Targets

- Four C-level record shapes are modeled and schema-exported.
- Focused tests cover the required starter fixtures in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS277.md`.
- Canonical hashing is stable under shuffled inputs.
- C consumes released A/B records and preserves their non-authority posture.
- No semantic adjudication, gate execution, probe execution, worker dispatch,
  implementation authority, product authority, official-eval authority, or
  future-family selection APIs are present in C.

## Implementation Readiness Notes

1. `OTB-0-C` is implementation-ready as a bounded deterministic pressure and
   handoff slice after starter-bundle acceptance.
2. Highest risks are laundering post-eval pressure into clean evidence and
   allowing handoff records to grant authority.
3. Recommended implementation order:
   - shared C vocabulary and canonical hashing;
   - delta attribution ledger models/builders;
   - stale object invalidation models/builders;
   - integration handoff models/builders;
   - family closeout alignment models/builders;
   - schema export and focused fixtures.
