# Assessment vNext+239 Edges

Status: pre-lock edge assessment for `V85-A`.

Authority layer: planning / pre-start scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS239_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Declaration Request Could Become Declaration Authority

- Lock containment:
  `V85-A` rows must carry non-authority posture and guardrail refs. Eligible
  requests remain candidates for later lookup review only.
- Expected result:
  contained if implemented.

### Edge 2: Session Identity Could Drift

- Lock containment:
  `semantic_declaration_session_ref` is required across request, act, witness,
  competency, and guardrail rows.
- Expected result:
  contained if validators reject mismatched session / candidate lineages.

### Edge 3: Candidate Status Could Become Selected Declaration

- Lock containment:
  `V85-A` may create declaration candidates only. Canonical lookup results
  belong to `V85-B`, and selected-for-later-obligation-expansion review belongs
  to `V85-C`.
- Expected result:
  contained if `declaration_selection_status = not_selected_by_v85a` is
  required for eligible starter rows.

### Edge 4: Support Doctrine Could Become Current-Turn Eligibility

- Lock containment:
  support, roadmap, Morphic UX, direct OAI, and meta-orchestrator rows may
  contextualize a request, but they cannot be the only eligibility sources.
- Expected result:
  contained if support-only eligibility rejects ship.

### Edge 5: Model Output Could Become Canonical Class Truth

- Lock containment:
  generated declaration candidates remain candidate-only unless source-bound
  by current witnesses and provenance. Unknown classes route to registry gap.
- Expected result:
  contained if generated-without-witness and nearest-class-repair rejects ship.

### Edge 6: Opaque Pointer Competency Could Become Natural Binding Truth

- Lock containment:
  `V85-A` does not create pointer lookup fixtures, and any opaque pointer
  source remains competency context only.
- Expected result:
  contained if opaque-pointer-as-natural-truth rejects ship.

### Edge 7: Ambiguity / Abstain / Registry Gap Could Be Smoothed Into Selection

- Lock containment:
  ambiguity, abstain, malformed input, and registry-gap states have explicit
  fail-closed postures.
- Expected result:
  contained if eligible rows reject ambiguous selected bindings and unknown
  class canonical claims.

### Edge 8: Negative Cues Could Be Ignored

- Lock containment:
  implementation-now, execute-now, runtime-authorize, productize, release,
  obligation-expand-now, skip-lookup, invent-class, and select-next-family
  cues are row-shaped and route to guardrails or future-family posture.
- Expected result:
  contained if negative-cue blockers cannot be eligible as ordinary selected
  declarations.

### Edge 9: Resident-Model Competency Could Be Treated As One Vague Capability

- Lock containment:
  competencies are independent row requirements: pointer obedience,
  artifact-shape obedience, bounded local judgment, uncertainty routing,
  order/duplicate preservation, unknown abstention, no unauthorized
  transition, and schema-bound stopping.
- Expected result:
  contained if row coverage is required instead of one exclusive enum.

### Edge 10: V85-A Could Ship V85-B/C Or V86 Surfaces

- Lock containment:
  the emitted record-shape set is limited to three `V85-A` surfaces.
- Expected result:
  contained if fixtures and validators reject lookup indexes, registries,
  summaries, handoffs, obligation expansion, and `V86` selection.

## Residual Edges

- `V85-B` must prove canonical lookup and registry behavior without obligation
  expansion.
- `V85-B` must separate operator semantics from class semantics, especially
  for authority-adjacent entries such as `GATE`, `router.dispatcher@v1`,
  `state.transition@v1`, and `worker.taskpack@v1`.
- `V85-C` must keep warning-ready posture narrow and must not skip from
  declaration directly to evidence, audit, or closeout routing without
  obligation expansion review as prerequisite pressure.
- Any later `V86`, canonical implementation-lock, Morphic UX, direct OAI,
  meta-orchestrator, product, graph, release, or recursive-policy family must
  be selected by a later selector or lock, not inferred from `V85-A`.

## Current Judgment

- `V85-A` is ready as a starter lock for semantic declaration request intake
  if the docs-only start gate passes.
- The slice preserves the intended boundary: it can record source-bound
  semantic declaration pressure from released `V84-C` substrate and current
  task context, but it does not perform canonical lookup, expand obligations,
  execute implementation, run commands, invoke tools, transition runtime,
  productize, create graph-memory authority, amend recursive policy, or select
  `V86`.
