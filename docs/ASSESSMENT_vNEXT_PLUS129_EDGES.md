# Assessment vNext+129 Edges

Status: planning-edge assessment for `V52-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS129_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Bridge Ownership Laundering Into `urm_domain_adeu`

- Risk:
  the imported prototype’s `urm_domain_adeu` overlay could become the de facto owner
  of the paper-semantic bridge seam.
- Response:
  instantiate the bridge in `urm_domain_paper` only and treat `urm_domain_adeu` as
  not selected for this slice.

### Edge 1A: Existing Paper-Domain Tool Supersession

- Risk:
  the new semantic-decomposition tool could silently replace or reinterpret the
  already released closed-world `paper.abstract` tool family inside
  `urm_domain_paper`.
- Response:
  make the new tool additive only, preserve `paper.abstract.pipeline.v0` as the
  existing default template, and require regression coverage for the existing paper
  tool flow.

### Edge 2: Browser State Becomes Authority

- Risk:
  `V52-B` route-local selections could become silent live bridge authority instead of
  remaining presentation-only browser state.
- Response:
  admit only released `adeu_paper_semantic_worker_request@1` as authoritative bridge
  input.

### Edge 3: Worker Prompt Mints A Parallel Semantic Layer

- Risk:
  bridge prompt compilation could silently redefine paper semantic meaning or relax
  the released `V52-A` source-authority / advisory-only posture.
- Response:
  consume released worker requests directly and forbid bridge-side repair of
  `operator_posture`, `constraints`, `return_schema`, or `request_hash`.

### Edge 4: Live Result Reinterpretation Drift

- Risk:
  the bridge could start parsing or rendering the returned semantic artifact and turn
  into a second semantic owner.
- Response:
  keep `V52-C` result payloads ref-only and evidence-bearing, not artifact-rendering.

### Edge 5: Surface Inflation Through New API/Web Seams

- Risk:
  the worker bridge could quietly widen into a new dedicated API route or live web
  fetch loop instead of staying inside bounded domain/harness surfaces.
- Response:
  keep the bridge on the existing URM tool-call surface only and forbid `apps/web`
  route changes in this slice.

### Edge 5A: Ambient Capability/Policy Assumption

- Risk:
  the new tool could be added without an explicit capability-lattice / policy action
  mapping because nearby paper-domain tools already exist.
- Response:
  require explicit policy/capability mapping and bounded regression coverage for the
  new tool name rather than assuming ambient authorization.

### Edge 6: Prototype Workflow Overlay Laundering

- Risk:
  the imported workflow/template overlay could be copied into live repo code and set
  bridge semantics by precedent instead of by repo-owned contracts.
- Response:
  use the overlay as shaping evidence only and re-author the bridge in repo-native
  `urm_domain_paper` paths.

## Current Judgment

- `V52-C` is worth implementing next because it is the narrowest live worker seam that
  can prove the released `V52-A` paper-semantic worker request is usable in repo-owned
  domain/harness execution without widening the browser route.
- the slice should stay contract-subordinate, `urm_domain_paper`-owned, result-ref
  only, and explicit about non-selection of browser-trigger wiring and prototype
  workflow overlay ownership.
- it should also stay explicitly additive with respect to the already released
  `urm_domain_paper` abstract-tool lane rather than implicitly superseding it.
