# Draft ADEU ODEU Transition Broker OTB-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `OTB-0`.

Authority layer: support.

This note maps likely implementation surfaces for the `OTB-0` family. It does
not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Family Intent

`OTB-0` should make phase-transition legality deterministic after phase
artifacts, bridge contracts, and evidence references have been supplied by
planning docs, orchestration records, workers, or upstream broker outputs.

It should answer:

```text
Given this phase circuit, bridge contract, artifact set, evidence set, and
claimed next phase, is this transition structurally legal and what remains in
the next legal frontier?
```

It must not answer:

```text
Is the phase output semantically correct?
Should this ontology node apply?
Should probes run?
Should code be patched?
What is the product truth?
What official score changed?
```

## Recommended Package Shape

Likely package ownership:

- `packages/adeu_transition_broker`

Likely schema mirror:

- `spec/adeu_transition_broker/`

Likely package modules:

- `packages/adeu_transition_broker/src/adeu_transition_broker/models.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/vocabulary.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/catalog.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/bridge.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/validation.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/frontier.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/closure.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/baton.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/attribution.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/invalidation.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/hashing.py`
- `packages/adeu_transition_broker/src/adeu_transition_broker/export_schema.py`

Later starter locks may narrow this shape.

## Family Slices

| Slice | Implementation posture |
|---|---|
| `OTB-0-A` | Implement first. Phase catalog, bridge contracts, transition validation, legal frontier, non-authority guardrails. |
| `OTB-0-B` | Implement later. Transition closure, gate plans, worker baton contracts, evidence posture plans, operationalization reports. |
| `OTB-0-C` | Implement later. Delta attribution, stale phase-object invalidation, integration handoff, closeout alignment. |

## Shared Vocabulary

The family should use one canonical vocabulary source exported to schema.

Minimum shared enums:

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
- `closure_status`
- `handoff_posture`

No slice should define overlapping strings independently.

## Family Data Flow

```text
phase circuit catalog
  + bridge contract
  + transition claim
  + artifact rows
  + evidence rows
  + obligation transfer rows
  -> OTB-0-A transition validation
  -> legal frontier
  -> OTB-0-B closure/gate/baton planning
  -> OTB-0-C delta attribution and stale-object invalidation
```

## Non-Authority Boundary

`OTB-0` may validate transition records, emit blockers, and plan later
transition gates. It may not decide semantic truth, run tools, dispatch workers,
patch source, grant product authority, or select future families.

## Integration Boundaries

HOB integration:

```text
HOB ledgers and closure reports can be consumed as phase artifacts.
OTB does not recompute HOB inheritance or closure.
```

Semantic compiler integration:

```text
Semantic compiler blocks can be consumed as phase artifacts.
OTB does not rewrite semantic compiler blocks.
```

ProgramBench methodology integration:

```text
ProgramBench reconstruction phases can be represented as circuit phases.
OTB validates transitions such as scout -> schema re-entry, probe plan ->
reference observation, local parity -> packaged preflight, and packaged
preflight -> official eval.
```

No integration is selected by this mapping draft.

## Family Acceptance Theme

The family should be considered complete only when it can prove:

```text
inside-phase artifact production
  !=
legal cross-phase transition
```

and can deterministically block:

- stale artifact reuse;
- forbidden evidence contamination;
- transitive evidence contamination through derived artifacts;
- skipped required objects;
- silent obligation loss;
- incomplete but internally consistent bridges;
- readiness overpromotion;
- unsupported posture claims that need downgrade;
- illegal official-eval handoff;
- non-authorized worker or implementation baton claims.
