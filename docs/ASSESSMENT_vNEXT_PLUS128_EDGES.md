# Assessment vNext+128 Edges

Status: post-closeout edge assessment for `V52-B` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS128_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Browser Layer Becomes Second Semantic Owner

- Risk:
  `apps/web` could start minting paper-semantic meaning locally instead of behaving
  as a bounded consumer of released `V52-A` artifacts.
- Response:
  keep the route subordinate to released `adeu_paper_semantics` artifacts, preserve
  released semantic-law fields visibly, and forbid renderer-level semantic
  reinterpretation.
- Closeout Evidence:
  route-local view model retains `semantic_hash`, `identity_field_names`, and
  `projection_field_names`, while the route consumes only committed released
  `V52-A` artifacts.

### Edge 2: Fixture Stack Drift

- Risk:
  the workbench could silently widen from committed released artifact fixtures into
  ad hoc mock payloads or partial local JSON approximations.
- Response:
  admit only the committed released abstract and paragraph fixtures and validate each
  sample against the released artifact shape before rendering.
- Closeout Evidence:
  `sample-artifacts.ts`, `parsePaperSemanticArtifact(...)`, and committed fixtures
  under `packages/adeu_paper_semantics/tests/fixtures/v52a/`.

### Edge 3: Local Projection Mismatch Drift

- Risk:
  the route could silently fall back from a missing local projection and mask a real
  contract mismatch between released artifact data and route-local view config.
- Response:
  fail closed when the selected surface lacks a matching released projection.
- Closeout Evidence:
  `INVALID_SELECTED_SURFACE_PROJECTION` handling and the dedicated route-contract
  regression in `paper-semantic-workbench-contract.test.ts`.

### Edge 4: Diagnostic Vocabulary Laundering

- Risk:
  unsupported diagnostic kinds or severities in committed sample JSON could slip
  through local parsing and create a second browser-side diagnostic contract.
- Response:
  reject unsupported diagnostic enums before view-model construction.
- Closeout Evidence:
  parser validation of `diagnostic_kind` / `severity` and the
  `reject_invalid_diagnostic_kind.json` regression.

### Edge 5: Live Worker / API Laundering

- Risk:
  the mock workbench could quietly become a thin UI over live worker or API behavior,
  collapsing the intended `V52-B` to `V52-C` boundary.
- Response:
  keep `V52-B` read-only and local, with no `fetch`, no worker bridge, and no
  harness/domain registration in the route.
- Closeout Evidence:
  import guard coverage in `paper-semantic-workbench-contract.test.ts` and the
  bounded route source set under `apps/web/src/app/papers/semantic-workbench/`.

### Edge 6: Existing `/papers` Surface Creep

- Risk:
  the bounded workbench route could turn into a broader retrofit of the existing
  `/papers` route or product navigation surface.
- Response:
  keep `V52-B` bounded to one direct route only and do not treat the existing papers
  page as route-expansion authorization.
- Closeout Evidence:
  shipped scope is the direct `/papers/semantic-workbench` route only, with no
  broader `apps/web/src/app/papers/page.tsx` retrofit in the merged diff.

### Edge 7: Prototype Visualization / Overlay Laundering

- Risk:
  the imported overlay route, helper files, or spatial scene could re-enter as
  first-slice browser authority.
- Response:
  re-author the route entirely in repo-native `apps/web` paths and keep advanced
  visualization deferred.
- Closeout Evidence:
  shipped code exists only under `apps/web/src/app/papers/semantic-workbench`, while
  the imported bundle remains under
  `examples/external_prototypes/adeu-paper-semantic-workbench-poc`.

### Edge 8: Runtime / Build Portability Drift

- Risk:
  a bounded route could pass local contract tests yet fail real Next build/runtime
  constraints through unsupported import posture or runtime-only helpers.
- Response:
  keep the route build-safe under the live `apps/web` toolchain and validate it with
  the local bounded web build lane.
- Closeout Evidence:
  merged validation included `npm run build`, and the route-local loader/import path
  was hardened to satisfy the live web CI lane.

## Current Judgment

- `V52-B` was the right second D-track move because it proved the released paper
  semantic contracts could drive a real browser-facing route without widening into
  live worker execution.
- the shipped result remains properly bounded: one direct workbench route only, one
  committed-sample registry over released abstract/paragraph artifacts only, explicit
  selected-sample-ref versus artifact-id split, preserved semantic-law visibility,
  deterministic claim ordering, fail-closed fixture/projection validation, and no
  fetch/live-worker/prototype-sprawl widening.
- review hardening materially improved the release by closing the missing-surface
  projection fallback gap, rejecting invalid diagnostic enums before render, and
  tightening the import guard/build compatibility posture.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` and `V52-B`
  closed on `main` and the branch-local default next path advanced to `V52-C` /
  `vNext+129`.
