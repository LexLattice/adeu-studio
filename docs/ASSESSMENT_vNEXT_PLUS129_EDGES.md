# Assessment vNext+129 Edges

Status: post-closeout edge assessment for `V52-C` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS129_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Bridge Ownership Laundering Into `urm_domain_adeu`

- Risk:
  the paper-semantic bridge could quietly migrate into `urm_domain_adeu` and make the
  imported overlay’s ownership claim real by drift.
- Response:
  keep the live bridge instantiated only inside the existing `urm_domain_paper`
  domain pack and treat `urm_domain_adeu` as not selected for this seam.
- Closeout Evidence:
  shipped bridge code exists in `packages/urm_domain_paper/src/urm_domain_paper/`,
  while no bridge-owner implementation landed in `urm_domain_adeu`.

### Edge 2: Existing Paper-Domain Tool Supersession

- Risk:
  `paper.run_semantic_decomposition` could silently replace or reinterpret the
  already released closed-world `paper.abstract` tool family and its default template.
- Response:
  keep the new tool additive, preserve `paper.abstract.pipeline.v0` as the existing
  default, and require regression coverage for the existing paper tool flow.
- Closeout Evidence:
  retained default template and existing tool names in `adapters.py`, plus regression
  coverage in `apps/api/tests/test_urm_domain_tools.py`.

### Edge 3: Browser State Becomes Bridge Authority

- Risk:
  `V52-B` route-local selections could become silent bridge authority instead of
  remaining presentation-only browser state.
- Response:
  admit only released `adeu_paper_semantic_worker_request@1` as authoritative bridge
  input.
- Closeout Evidence:
  `RunSemanticDecompositionArgs` validates only `worker_request`, and the bridge never
  consumes route-local `selected_surface`, `focus_claim_id`, or similar browser data.

### Edge 4: Live Result Reinterpretation Drift

- Risk:
  the bridge could begin parsing or rendering the returned semantic artifact and turn
  into a second semantic owner instead of a bounded worker-bridge seam.
- Response:
  keep `V52-C` result payloads ref-only and evidence-bearing, not artifact-rendering.
- Closeout Evidence:
  `PaperSemanticWorkerBridgeResult` carries `artifact_ref`, `warrant_tag`, and
  worker/evidence refs only; it does not embed or re-render the artifact payload.

### Edge 5: Ambient Capability/Policy Assumption

- Risk:
  the new tool could appear in the domain pack without explicit capability-lattice /
  policy mapping because neighboring paper tools already exist.
- Response:
  require explicit policy/capability mapping and dedicated regression coverage for the
  new tool name.
- Closeout Evidence:
  `paper.run_semantic_decomposition` was added to both capability-lattice copies and
  is exercised in `apps/api/tests/test_urm_capability_policy.py`.

### Edge 6: Surface Inflation Through New API Or Web Seams

- Risk:
  the worker bridge could quietly widen into a dedicated paper-semantics API route or
  browser-trigger flow instead of staying inside bounded domain/harness surfaces.
- Response:
  keep the bridge on the existing URM tool-call surface only and forbid `apps/web`
  route changes in this slice.
- Closeout Evidence:
  merged scope is bounded to `urm_domain_paper`, `apps/api` URM route integration, and
  policy files only; no `apps/web` route changes shipped in `v129`.

### Edge 7: Invalid Worker Result Or Runtime Mismatch Fails Open

- Risk:
  malformed returned artifact payloads or runtime/config mismatches could be coerced
  into apparent success and blur bridge accountability.
- Response:
  fail closed on invalid request, invalid returned artifact payload, and runtime
  bridge/config mismatch.
- Closeout Evidence:
  `fail_closed_invalid_request` and `fail_closed_bridge_config_mismatch` paths in
  `adapters.py`, plus dedicated regression tests in
  `apps/api/tests/test_urm_domain_tools.py`.

### Edge 8: Prototype Workflow Overlay Laundering

- Risk:
  the imported workflow/template overlay could be copied into live repo code and set
  bridge semantics by precedent instead of by repo-owned contracts.
- Response:
  use the overlay as shaping evidence only and re-author the bridge in repo-native
  `urm_domain_paper` plus existing URM surfaces.
- Closeout Evidence:
  shipped code lives only in repo-native `packages/urm_domain_paper`, `apps/api`, and
  policy paths, while the prototype remains under
  `examples/external_prototypes/adeu-paper-semantic-workbench-poc`.

## Current Judgment

- `V52-C` was the right third D-track move because it proved the released
  `V52-A` paper-semantic worker request can drive a real repo-owned worker seam
  without widening the browser route or importing the prototype workflow overlay.
- the shipped result remains properly bounded: one additive tool only, one retained
  default abstract template, one explicit capability-policy mapping, one refs-only
  bridge result posture, and no dedicated API or browser-trigger widening.
- the release also stayed additive with respect to the already shipped
  `urm_domain_paper` tool family rather than implicitly superseding it.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` through
  `V52-C` closed on `main` and the branch-local default next path advanced to `V52-D`
  / `vNext+130`.
