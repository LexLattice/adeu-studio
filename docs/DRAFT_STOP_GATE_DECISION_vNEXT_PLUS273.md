# Draft Stop-Gate Decision vNext+273

Status: starter decision draft for `HOB-0-B`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS273.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+273` / `HOB-0-B` only.
- It may activate closure reports, next-frontier reports, plan-only probe
  matrix rows, bounded implementation batch contracts, and operationalization
  reports over released `HOB-0-A` artifacts.
- It does not authorize semantic adjudication by the broker, ontology
  generation, catalog mutation by the broker, probe execution, command
  execution outside the implementation/test lane, worker dispatch, product
  behavior claims, ProgramBench integration, score attribution, delta
  attribution, stale-ledger invalidation, integration handoff, future-family
  selection, release authority, or recursive policy amendment.

## Starter Inputs

- selector draft:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
- architecture / decomposition:
  - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS273.md`
- edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS273_EDGES.md`
- implementation mapping:
  - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_HOB_0B_IMPLEMENTATION_MAPPING_v0.md`
- released A closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md`
  - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`
  - `artifacts/agent_harness/v272/evidence_inputs/hob_0a_closeout_evidence_v272.json`
- released A package surfaces:
  - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0a.py`
  - `packages/adeu_obligation_broker/tests/test_hob_0a.py`
  - `packages/adeu_obligation_broker/schema/`

## Starter Exit Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Family selector names `HOB-0-B` as next default candidate after A | required | `planned` | `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md` |
| Released A closeout exists | required | `planned` | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md` |
| Slice B consumes A records only | required | `planned` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS273.md` |
| Closure basis vocabulary is explicit | required | `planned` | starter vocabulary |
| Parent readiness cannot exceed weakest required child | required | `planned` | validation rules |
| Representative-only branches cannot be marked fixed/gold | required | `planned` | validation rules |
| Probe matrix rows are plan-only, not observed | required | `planned` | `probe_authority_posture` |
| Batch contracts remain bounded and non-dispatching | required | `planned` | batch contract posture |
| Deterministic canonical hash fixture required | required | `planned` | starter fixtures |
| C delta attribution and stale-ledger invalidation remain deferred | required | `planned` | deferred section |

## Recommendation

- gate decision:
  - `HOB_0B_STARTER_READY_FOR_IMPLEMENTATION_AFTER_REVIEW`
- rationale:
  - the starter bundle keeps `HOB-0-B` narrow;
  - it computes closure and operationalization planning from released A
    records without reopening semantic applicability or running probes;
  - B can prove readiness aggregation, frontier prioritization, probe-plan
    non-observation, and bounded batch contracts before C adds delta
    attribution and stale-ledger invalidation.
