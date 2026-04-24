# Assessment vNext+188 Edges

Status: pre-lock edge assessment for planned `V68-A` (April 24, 2026 UTC).

Authority layer: planning.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS188_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Cartography Could Become Scheduling Authority

- Risk:
  a whole-series map could be overread as selecting the next family or slice.
- Response:
  keep `V68-A` descriptive and non-authorizing. Scheduling still requires planning
  and lock posture outside the map output.

### Edge 2: Mentioned Review Could Become Admitted Source

- Risk:
  external review could be conversationally mentioned and then treated as
  integrated evidence without an artifact.
- Response:
  require explicit source-status and source-presence posture. The captured GPTPro
  reviews are now integrated support-layer shaping sources because their support
  artifacts exist; missing future review artifacts must be marked
  `review_pending_input`, not `integrated_shaping_source`.

### Edge 3: Namespace Rows Could Collapse Distinct Identities

- Risk:
  `V67`, `V67-C`, `vNext+187`, `vnext_plus187`, and `arc/v67-r3` could be mapped as
  the same thing because their names are adjacent.
- Response:
  require namespace-kind rows and reject string-resemblance identity collapse.

### Edge 4: Closeout Evidence Could Be Overgeneralized

- Risk:
  closeout evidence for one implementation / closeout arc could be treated as proof
  about an entire family, future branch, product lane, or recursive lifecycle.
- Response:
  evidence rows must carry claim horizon and target namespace.

### Edge 5: Tool Applicability Could Be Overread

- Risk:
  a passing repo tool could be treated as supporting a claim outside the tool's
  actual namespace or declared surface.
- Response:
  require tool-applicability posture, including `namespace_limited` and
  `not_applicable_to_claim`.

### Edge 6: Deferred Branches Could Disappear

- Risk:
  `V43` and other non-selected branches could vanish from the current map because
  they are not in the immediate `V68` through `V75` path.
- Response:
  keep connected conditional and deferred branch posture first-class.

### Edge 7: Product Projection Could Pull The Family Too Far Forward

- Risk:
  the typed adjudication product wedge could pull `V68-A` into model-output
  comparison, operator workbench, or product bundle work.
- Response:
  keep product projection deferred to `V74`; `V68-A` may only make the map substrate
  that later product projection consumes.

### Edge 8: Starter Fixture Could Fake Historical Completeness

- Risk:
  a reference cartography fixture could look complete while only covering the
  post-`V67` current horizon.
- Response:
  require explicit `coverage_horizon` and allow truthful partial coverage with
  unknowns, rather than fake completeness.

### Edge 9: Namespace Enum Bloat Could Recreate Ambiguity

- Risk:
  near-duplicate namespace kinds, such as generic slice, implementation-arc,
  closeout-arc, or support-doc variants, could make the cartography object less
  precise than the prose it replaces.
- Response:
  keep namespace kinds tight and move source kind, authority layer, source status,
  and source presence posture into source-row fields rather than namespace kinds.

### Edge 10: Repo Cartography Schemas Could Be Misclassified

- Risk:
  `arc` in schema names could be read as ARC-AGI task lineage instead of repo ARC
  series cartography.
- Response:
  use `repo_*` schema names for this starter family and include a reject fixture
  proving repo cartography schema names cannot be classified as ARC-AGI challenge
  artifacts.

## Current Judgment

- `V68-A` is the right first slice after `V67` because later recursive lifecycle
  families need a current map before candidate intake, classification, ratification,
  integration, review, projection, or dispatch widening.
- The slice should remain deliberately finite:
  - schema/model/validator surfaces;
  - source-status posture;
  - namespace distinction;
  - separate closure and branch posture;
  - support lineage, evidence surface, and tool-applicability row shapes;
  - recursive-coordinate emission planning without authority.
- Implementation should stay in the repo-description lane unless review finds a
  stronger existing package boundary.
