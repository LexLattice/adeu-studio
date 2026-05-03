# Assessment vNext+233 Edges

Status: pre-lock edge assessment for `V83-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS233_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Intent Contract Could Become Implementation Authority

- Starter containment:
  `V83-A` selects only intent contract, source-index, and
  non-implementation guardrail rows. Implementation, work-packet execution,
  code edits, command execution, PR creation, commit, merge, release, and
  product authorization are forbidden by the lock.
- Expected implementation proof:
  validators reject any starter row that contains `V83-B` / `V83-C` surfaces,
  implementation refs, execution claims, or later-family selection.

### Edge 2: Recordability Could Become Eligibility

- Starter containment:
  source rows and intent rows must distinguish `intent_recordability_posture`
  from `semantic_spec_eligibility_posture`.
- Expected implementation proof:
  support-only, dogfood-only, absence-only, Morphic-only, external-doc-only,
  and generated-spec-only rows cannot use
  `eligible_for_semantic_spec_review`.

### Edge 3: Generated Model Or Agent Spec Could Become Truth

- Starter containment:
  generated source roles are allowed only as candidate review sources with
  `generation_posture` and `model_agent_authority_posture`.
- Expected implementation proof:
  model/agent output without prompt context, model/agent profile refs, bounded
  source refs, and candidate-only posture must reject when marked eligible.

### Edge 4: Support Docs Could Become Lock Authority

- Starter containment:
  Morphic UX, direct-harness, roadmap, and support doctrine sources may
  contextualize the family but cannot alone make a row eligible.
- Expected implementation proof:
  unavailable or external local sources are represented as repo-owned support,
  external-import rows, or explicit absence markers; fixtures do not
  reconstruct them from memory.

### Edge 5: Tests Could Become Semantic Closure

- Starter containment:
  `success_horizon_kind` must be typed, and "passes tests" cannot be the only
  success horizon for an eligible contract.
- Expected implementation proof:
  reject fixtures cover test-only success claims and prose-only semantic
  closure claims.

### Edge 6: Non-Goals Could Become Required Work

- Starter containment:
  eligible rows require source-bound `non_goal_refs`; `V83-A` does not yet map
  artifact obligations.
- Expected implementation proof:
  non-goal source rows remain non-goals and cannot appear as implementation
  obligations in the starter fixture.

### Edge 7: Authority Boundaries Could Become Permission

- Starter containment:
  authority-boundary refs are required for eligible contracts, while
  non-implementation guardrails forbid downstream authority.
- Expected implementation proof:
  authority boundary rows cannot authorize implementation, runtime,
  work-packet execution, product, release, graph memory, or policy amendment.

### Edge 8: Morphic UX Could Become Runtime UI Work

- Starter containment:
  Morphic UX v2 is a support/test-case source for semantic projection, not the
  umbrella family and not runtime UI authorization.
- Expected implementation proof:
  Morphic-only rows remain blocked, context-only, or scoped to future UX
  projection review; no runtime composer or renderer change is claimed.

### Edge 9: Direct OAI Harness Could Become Provider Runtime Authority

- Starter containment:
  direct-harness support docs can contribute provider capability / evidence /
  workflow-transition distinctions, not runtime authority.
- Expected implementation proof:
  direct OAI support rows cannot grant provider capability, tool execution,
  meta-orchestrator runtime transition, or live harness behavior.

### Edge 10: V83-A Could Select V84

- Starter containment:
  `V83-A` may carry future pressure but cannot select `V84` or any later
  family. Likely post-`V83` implementation work-packet activation review
  remains unselected until a future selector.
- Expected implementation proof:
  no fixture, schema, closeout, or handoff row claims `V84` selection.

## Residual Edges

- `V83-B` must later bind semantic relations, validation needs, and
  acceptance evidence to released `V83-A` intent rows without converting tests
  into semantic truth.
- `V83-B` must keep artifact obligations distinct from implementation.
- `V83-C` must keep projection packets and quality gates as review posture,
  not code correctness or work-packet authority.
- Any future Morphic UX, direct OAI, general digital artifact projection, or
  implementation work-packet activation family must be selected by later
  locks/selectors, not inferred from `V83-A`.

## Current Judgment

The `vNext+233` starter scope is ready for a bounded `V83-A` implementation
draft. The active implementation should ship only the source-bound semantic
intent contract, intent source index, and non-implementation guardrail
surfaces. The main risks are recordability/eligibility drift, generated-spec
authority drift, support-source authority drift, test-only semantic closure,
and Morphic/direct-OAI scope laundering; all are represented as required
starter validators and reject fixtures.
