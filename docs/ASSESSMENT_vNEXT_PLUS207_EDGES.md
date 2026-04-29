# Assessment vNext+207 Edges

Status: pre-lock edge assessment for `V74-B` (April 29, 2026 UTC).

Authority layer: draft assessment scaffold; not closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS207_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Typed Adjudication Could Become Ratification

- Risk:
  typed adjudication case views may be overread as adoption, ratification, or
  outcome truth.
- Required containment:
  typed case rows must remain projection substrate over released `V74-A` rows
  and must not create new ratification, adoption, outcome verdict, product, or
  release authority.

### Edge 2: Conceptual-Diff Support Could Be Laundered As Released Schema

- Risk:
  conceptual-diff support artifacts may be treated as released schema or
  architecture authority.
- Required containment:
  support docs may be source lineage only; released schema authority must come
  from emitted `repo_*` schema surfaces.

### Edge 3: Model Comparison Could Become Benchmark Truth

- Risk:
  model-output comparison projection may be overread as global model ranking,
  model selection, or benchmark result.
- Required containment:
  comparison projection must bind to fixed prompt, fixed outputs, fixed source
  rows, structured comparison axes, and non-benchmark guardrails.

### Edge 4: Comparison Axes Could Become Narrative Or Unbounded

- Risk:
  comparison axes could become prose-only claims with no bounded horizon.
- Required containment:
  axis rows must carry `axis_ref`, `axis_kind`, bounded claim horizon, source
  refs, observed difference posture, confidence posture, exception refs where
  needed, and non-benchmark guardrails.

### Edge 5: Model-Output Provenance Could Be Missing

- Risk:
  comparison projection could compare model outputs without prompt, model
  identity, captured output, or run-context refs.
- Required containment:
  model-output source rows must preserve prompt source, model identity, output
  capture, run context, source presence posture, and limitation note.

### Edge 6: Exceptions Could Be Hidden Or Resolved

- Risk:
  exception visibility rows could omit known blockers or mark exceptions
  resolved in `V74-B`.
- Required containment:
  exception rows must keep source gaps, dissent, regressions, review conflicts,
  evidence gaps, product/runtime/dispatch authority gaps, unchecked axes, and
  provenance gaps visible; `V74-B` must not resolve them.

### Edge 7: Product Wedge Could Become Product Authorization

- Risk:
  typed adjudication product-pressure cases could be interpreted as product
  selection.
- Required containment:
  product-pressure projection must remain product-authority-missing,
  future-product-review, rejected, or out-of-scope.

### Edge 8: V74-B Could Begin V74-C Or V75

- Risk:
  typed adjudication and exception visibility could drift into visibility
  contracts, workbench projection, post-projection handoff, or dispatch.
- Required containment:
  `V74-C` and `V75` remain deferred; no live UI, operator command surface,
  runtime permission, release, dispatch, or external contest participation
  lands in this slice.

### Edge 9: Source Absence Could Become Memory

- Risk:
  missing prompt, model-output, adjudicator-schema, or conceptual-diff source
  material could be reconstructed from prose.
- Required containment:
  absence remains row data with source presence posture, never unstated
  memory.

## Closeout Expectations

- A successful `V74-B` closeout should prove that typed adjudication,
  model-output comparison, and exception visibility are machine-checkable and
  source-bound.
- It should preserve the V74 authority boundary: projection improves operator
  legibility, but does not ratify, adopt, implement, productize, release, grant
  runtime permission, dispatch, or select a model globally.
