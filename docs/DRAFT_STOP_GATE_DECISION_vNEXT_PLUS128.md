# Draft Stop-Gate Decision vNext+128

Status: proposed gate for `V52-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS128.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the live route is exactly `/papers/semantic-workbench`;
- the route consumes only the committed released `V52-A` artifact fixtures;
- every committed sample fixture is validated against released `PaperSemanticArtifact`
  shape before rendering;
- the default first render selects the committed abstract artifact and reaches
  `ready_clean`;
- the route preserves released `adeu_paper_semantic_artifact@1` payloads, including
  `semantic_hash`, `identity_field_names`, and `projection_field_names`, and adds
  only bounded local view helpers;
- `selected_sample_artifact_ref` remains the committed fixture-path identity while
  `artifact_ref` remains the released artifact-id identity;
- claim ordering follows released `projection.claim_order` when present and only falls
  back to deterministic claim-id order otherwise;
- the route renders the bounded workbench sections:
  - source metadata
  - authority posture
  - anchored spans
  - claims
  - lane fragments
  - inference bridges
  - diagnostics
  - projections
- no direct API, live-worker, domain-registration, or prototype spatial-scene surface
  exists under the route implementation;
- route smoke and bounded interaction/contract tests pass deterministically.

## Do Not Accept If

- the route fetches live semantic data or bridges directly into worker execution;
- `fail_closed_invalid_fixture_stack` is used loosely enough to hide fixture-shape,
  missing-field, or local projection mismatch failures;
- freeform text entry, upload-based processing, or runtime semantic generation ships
  in this slice;
- the route redefines diagnostic meaning or paper semantic authority in `apps/web`;
- the prototype overlay route or helper modules are imported as live authority;
- advanced spatial visualization or broader workbench sprawl appears in the first web
  slice.

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=128`
- once implementation starts:
  - run the relevant `apps/web` lint plus route smoke/contract tests for the bounded
    `V52-B` surface.
