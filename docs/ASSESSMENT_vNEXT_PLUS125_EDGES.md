# Assessment vNext+125 Edges

Status: pre-lock edge assessment for `V51-B` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS125_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: API Becomes Second Kernel Owner

- Risk:
  route code could silently re-implement engine behavior or reinterpret kernel facts,
  making `apps/api` a second owner of simulation semantics.
- Planned Response:
  keep the route kernel-subordinate, require `run_canonical_scenario(...)`, and
  project released `V51-A` outputs only.

### Edge 2: Persistent Session Laundering

- Risk:
  the prototype reset/step/state trilogy could reappear as mutable route state or
  `app.state.sim` under the first API slice.
- Planned Response:
  freeze `V51-B` as stateless `POST /odeu-sim/run` only and forbid reset/step/state
  session surfaces.

### Edge 3: Projection Widening Drift

- Risk:
  the API response could widen into full UI payload or network/agent-detail sprawl
  before the route seam is accepted.
- Planned Response:
  freeze one summary-only JSON response posture over released kernel facts.

### Edge 4: Invalid-Request Drift

- Risk:
  unsupported scenario names, invalid step counts, or forbidden override fields could
  be silently repaired instead of failing closed.
- Planned Response:
  keep typed invalid-request posture explicit, require non-negative seeds, and forbid
  scenario overrides.

### Edge 5: Projection-Law Drift

- Risk:
  the route could emit a different `lane_summary`, a truncated metric object, or a
  zero-filled action vocabulary even while claiming to stay subordinate to the kernel.
- Planned Response:
  freeze the response projection law: full released metric payload, exact three-key
  lane summary, and sparse observed-only action counts.

### Edge 6: Kernel-Stack Compatibility Drift

- Risk:
  the route could run against an unexpected kernel contract or silently absorb later
  kernel drift without one typed mismatch carrier.
- Planned Response:
  carry one explicit kernel-contract ref in the response and fail closed on mismatch.

### Edge 7: Deterministic Replay Drift

- Risk:
  identical route requests could produce different JSON ordering or summary payloads
  even when the released kernel remains deterministic.
- Planned Response:
  freeze deterministic request/response hashing and committed replay fixtures over the
  admitted starter scenarios.

### Edge 8: Product-Surface Creep

- Risk:
  browser/UI work, persistent storage, or broader product routing could leak into the
  first API slice and blur family ownership.
- Planned Response:
  keep `V51-B` bounded to one route module, targeted tests, and deterministic
  fixtures only.

### Edge 9: Prototype API Precedent Laundering

- Risk:
  the imported prototype `api.py` could be copied into live paths wholesale and treat
  prototype choices as released authority.
- Planned Response:
  re-author the route in repo-native `apps/api` paths and keep the prototype API as
  shaping evidence only.
