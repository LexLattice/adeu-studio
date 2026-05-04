# Assessment vNext+240 Edges

Status: pre-lock edge assessment for `V85-B`.

Authority layer: planning / pre-start scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS240_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Canonical Lookup Could Become Semantic Truth

- Lock containment:
  lookup rows must carry review-only posture, pointer competency horizon, and
  non-authority guardrail refs. Exact lookup is not natural-language truth.
- Expected result:
  contained if validators reject lookup-as-truth claims.

### Edge 2: Opaque Pointer Success Could Prove Natural Binding

- Lock containment:
  opaque pointer fixtures prove pointer obedience only. Natural binding
  correctness remains unclaimed and must require separate source-bound review.
- Expected result:
  contained if opaque-fixture-as-natural-binding rejects ship.

### Edge 3: Pointer Grammar Could Repair Unknown Inputs

- Lock containment:
  malformed pointers, unknown operators, unknown classes, unknown versions,
  ambiguous parses, and abstain-required inputs are explicit parse postures.
- Expected result:
  contained if unknown and malformed inputs fail closed.

### Edge 4: Alias Or Version Handling Could Become Implicit Normalization

- Lock containment:
  alias acceptance requires alias rows, and unknown versions cannot normalize
  to latest versions without a declared rule.
- Expected result:
  contained if alias-missing and unknown-version-latest rejects ship.

### Edge 5: Duplicate Or Order Semantics Could Be Lost

- Lock containment:
  lookup and fixture rows carry order and duplicate preservation posture.
  Reordering or deduplication requires explicit normalization posture.
- Expected result:
  contained if duplicate-collapse and order-change rejects ship.

### Edge 6: Registry Entries Could Become Runtime Behavior

- Lock containment:
  operator and class registry rows must distinguish declaration semantics from
  runtime behavior, implementation targets, and authority.
- Expected result:
  contained if `GATE`, `ROUTE`, `TRANSITION`, `worker.taskpack@v1`, and
  similar entries remain declaration-only.

### Edge 7: Obligation-Family Lookup Could Become Obligation Expansion

- Lock containment:
  obligation-family rows may name families for later expansion only and must
  carry expansion-not-authorized posture.
- Expected result:
  contained if concrete obligation expansion inside `V85-B` rejects.

### Edge 8: Support Context Could Mint Registry Entries

- Lock containment:
  support docs may contextualize registries but cannot invent operator,
  class, alias, or obligation-family rows without source-bound registry
  evidence.
- Expected result:
  contained if model-prose and support-only invented-entry rejects ship.

### Edge 9: Session / Candidate Lineage Could Drift

- Lock containment:
  lookup, registry, obligation-family, and fixture rows must preserve
  `semantic_declaration_session_ref`, `candidate_ref`, and released `V85-A`
  request lineage.
- Expected result:
  contained if mismatched lineage rejects ship.

### Edge 10: V85-B Could Ship V85-C Or V86 Surfaces

- Lock containment:
  emitted record-shape set is limited to four `V85-B` surfaces.
- Expected result:
  contained if summaries, handoffs, obligation expansion, evidence contracts,
  audit taskpacks, deterministic transition tables, and `V86` selection reject.

## Residual Edges

- `V85-C` must summarize declaration lookup posture without treating lookup as
  selected obligation expansion or later-family selection.
- `V85-C` must split immediate obligation-expansion pressure from downstream
  evidence, audit, deterministic closeout, implementation-lock, Morphic UX,
  direct OAI, meta-orchestrator, product, graph, release, and recursive-policy
  pressure.
- Any later `V86`, obligation expansion, evidence contract, reviewer/auditor
  taskpack, transition table, implementation lock, runtime, product, graph, or
  recursive-policy family must be selected by a later lock or selector, not
  inferred from `V85-B`.

## Current Judgment

- `V85-B` is ready as a starter lock for canonical meta lookup / registry /
  semantic pointer fixture review if the docs-only start gate passes.
- The slice preserves the intended boundary: it can make pointer lookup,
  operator/class registry, obligation-family registry, and fixture behavior
  reviewable, but it does not expand obligations, execute implementation, run
  commands, invoke tools, transition runtime, productize, create graph-memory
  authority, amend recursive policy, or select `V86`.
