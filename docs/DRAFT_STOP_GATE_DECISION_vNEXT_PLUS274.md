# Draft Stop-Gate Decision vNext+274

Status: starter decision draft for `HOB-0-C`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS274.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+274` / `HOB-0-C` only.
- It may activate delta attribution ledgers, stale-ledger invalidation reports,
  pressure-only integration handoff rows, and family closeout alignment over
  released `HOB-0-A` and `HOB-0-B` artifacts.
- It does not authorize semantic adjudication by the broker, closure
  recomputation outside released B records, ontology generation, catalog
  mutation by the broker, probe execution, command execution outside the
  implementation/test lane, worker dispatch, product behavior claims,
  ProgramBench integration, clean product truth claims, score-to-closure
  laundering, future-family selection, release authority, or recursive policy
  amendment.

## Starter Inputs

- selector draft:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
- architecture / decomposition:
  - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS274.md`
- edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md`
- implementation mapping:
  - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_HOB_0C_IMPLEMENTATION_MAPPING_v0.md`
- released A closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md`
  - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`
  - `artifacts/agent_harness/v272/evidence_inputs/hob_0a_closeout_evidence_v272.json`
- released B closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS273.md`
  - `docs/ASSESSMENT_vNEXT_PLUS273_EDGES.md`
  - `artifacts/agent_harness/v273/evidence_inputs/hob_0b_closeout_evidence_v273.json`
- released package surfaces:
  - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0a.py`
  - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0b.py`
  - `packages/adeu_obligation_broker/tests/test_hob_0a.py`
  - `packages/adeu_obligation_broker/tests/test_hob_0b.py`
  - `packages/adeu_obligation_broker/schema/`

## Starter Exit Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Family selector names `HOB-0-C` as next default candidate after B | required | `planned` | `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md` |
| Released A and B closeouts exist | required | `planned` | v272/v273 closeout docs and evidence inputs |
| C consumes released A/B records only | required | `planned` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS274.md` |
| Delta attribution rows cite known numbered nodes | required | `planned` | starter vocabulary |
| Evidence boundary posture is required per attribution row | required | `planned` | validation rules |
| Score movement cannot become macro closure without closure evidence | required | `planned` | validation rules |
| Stale catalog hashes invalidate prior ledgers | required | `planned` | invalidation report vocabulary |
| Handoff rows remain pressure-only and non-selecting | required | `planned` | handoff posture fields |
| Family closeout cannot hide unresolved blockers | required | `planned` | validation rules |
| Deterministic canonical hash fixture required | required | `planned` | starter fixtures |

## Recommendation

- gate decision:
  - `HOB_0C_STARTER_READY_FOR_IMPLEMENTATION_AFTER_REVIEW`
- rationale:
  - the starter bundle keeps `HOB-0-C` narrow;
  - it attributes pressure to numbered obligations without laundering
    post-eval pressure or score movement into clean semantic evidence;
  - it closes the family only after released A, released B, C attribution,
    stale-ledger handling, and pressure-only handoff boundaries are explicit.
