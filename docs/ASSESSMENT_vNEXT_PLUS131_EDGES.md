# Assessment vNext+131 Edges

Status: planning-edge assessment for `V44-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS131_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V46` Benchmark Law Bleeds Upstream Into `V44-A`

- Risk:
  the first structural-assessment slice could mint benchmark-family or scoring doctrine
  before the assessment contracts themselves are frozen.
- Response:
  keep `V44-A` limited to probe and trace contracts only, with `V46` remaining a later
  consumer of those contracts rather than their upstream author.

### Edge 2: Hierarchical Fidelity Remains Prose-Only

- Risk:
  the newly aligned three-way split could remain rhetorical if the first released
  contracts do not type:
  - top-level plan spine
  - active-step descent
  - return-to-parent evidence
- Response:
  freeze explicit hierarchical probe and trace anchors in the first slice rather than
  deferring them to scoring code.

### Edge 3: Blocked And Invalid Closure Collapse

- Risk:
  the implementation could over-compress structural outcomes and erase the distinction
  between lawful insufficiency and invalid completion claims.
- Response:
  freeze both postures in the starter vocabularies and require reject fixtures for
  posture mismatch.

### Edge 4: Probe Family Widens Too Early

- Risk:
  the first slice could overreach into recursive depth, invariance suites, or broad
  probe libraries before the canonical probe/trace pair is stable.
- Response:
  keep `V44-A` to one small starter class set and defer wider libraries to `V44-D`.

### Edge 5: Taxonomy And Profile Surfaces Arrive Prematurely

- Risk:
  the implementation could ship normalized failure taxonomy or model-profile fields as
  part of the first trace contract, making `V44-B` retroactively authorless.
- Response:
  forbid taxonomy/profile outputs in `V44-A` and reserve them explicitly for `V44-B`.

### Edge 6: External Bundle Becomes Silent Authority

- Risk:
  the imported reasoning-benchmark package could quietly set the contract shapes for
  `V44-A` even though its real code target is mostly `V46`.
- Response:
  use the imported bundle only as support evidence for hierarchical split vocabulary;
  re-author `V44-A` contracts from repo-owned planning docs, not from the external
  package tree.

## Current Judgment

- `V44-A` is the right next move because it freezes the structural-assessment object
  before `V46` turns that object into benchmark substrate and scoring surfaces.
- the slice should remain small and contract-first:
  - one probe schema
  - one trace schema
  - starter flat/hierarchical fixtures
  - no taxonomy, profile, or benchmark metrics
- if the first implementation bundle stays that narrow, it should let the repo move
  into `V46` quickly without allowing the benchmarking package to mint assessment law.
