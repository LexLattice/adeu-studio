# Draft Stop-Gate Decision vNext+272

Status: starter decision draft for `HOB-0-A`.

Authority layer: planning / starter gate.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+272` / `HOB-0-A` only.
- It may activate the catalog, activation assessment, inherited obligation
  ledger, traversal validation, next-frontier, and non-authority guardrail seam.
- It does not authorize semantic adjudication by the tool, ontology generation,
  catalog mutation by the tool, probe execution, command execution outside the
  implementation/test lane, worker dispatch, implementation batches, product
  authority, semantic compiler integration, ProgramBench integration, future
  family selection, release authority, or recursive policy amendment.

## Starter Inputs

- selector draft:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
- architecture / decomposition:
  - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS272.md`
- edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`
- support inputs:
  - `docs/support/v16_meta_program_operationalization_robustness_patch.md`
  - `docs/support/v17_deterministic_hierarchical_meta_ontology_enforcement.md`
  - `docs/support/principled_recursive_odeu_meta_program_experimental_v15.md`
  - `docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md`
  - `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Starter Exit Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Family selector names `HOB-0` | required | `planned` | `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md` |
| Architecture doc separates model judgment from broker traversal | required | `planned` | `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md` |
| Slice A boundary excludes closure aggregation and probe matrices | required | `planned` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS272.md` |
| Catalog id/version/hash required | required | `planned` | starter vocabulary |
| Structured proof rows required for proof-sensitive statuses | required | `planned` | starter vocabulary |
| `not_inherited` and `optional_observed` escape hatches constrained | required | `planned` | validation rules |
| Next-frontier rows are primary A output | required | `planned` | output contract |
| Deterministic canonical hash fixture required | required | `planned` | starter fixtures |
| Non-authority guardrail denies semantic/tool/implementation authority | required | `planned` | guardrail vocabulary |

## Recommendation

- gate decision:
  - `HOB_0A_STARTER_READY_FOR_IMPLEMENTATION_AFTER_REVIEW`
- rationale:
  - the starter bundle keeps `HOB-0-A` narrow;
  - it validates deterministic traversal consequences after model semantic
    activation, without letting the broker become the semantic judge;
  - the first implementation can prove the institutional move with a small,
    deterministic fixture set before later slices add closure summaries,
    probe-matrix plans, implementation batches, and delta attribution.
