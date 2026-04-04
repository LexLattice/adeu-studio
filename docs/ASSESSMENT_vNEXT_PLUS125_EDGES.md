# Assessment vNext+125 Edges

Status: post-closeout edge assessment for `V51-B` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS125_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: API Becomes Second Kernel Owner

- Risk:
  route code could silently re-implement engine behavior or reinterpret kernel facts,
  making `apps/api` a second owner of simulation semantics.
- Response:
  keep the route kernel-subordinate, require `run_canonical_scenario(...)`, and
  project released `V51-A` outputs only.
- Closeout Evidence:
  `run_canonical_scenario(...)`, `summarize_lane_state(...)`, and
  `summarize_action_counts(...)` consumption in
  `apps/api/src/adeu_api/odeu_sim.py`, plus
  `test_build_odeu_run_response_uses_released_stateless_kernel_helper`.

### Edge 2: Persistent Session Laundering

- Risk:
  the prototype reset/step/state trilogy could reappear as mutable route state or
  `app.state.sim` under the first API slice.
- Response:
  freeze `V51-B` as stateless `POST /odeu-sim/run` only and forbid reset/step/state
  session surfaces.
- Closeout Evidence:
  shipped surface limited to `POST /odeu-sim/run`, absence of route-side simulation
  storage in `apps/api/src/adeu_api/odeu_sim.py`, and absence of any reset/step/state
  or session-token endpoints on `main`.

### Edge 3: Projection Widening Drift

- Risk:
  the API response could widen into full UI payload or network/agent-detail sprawl
  before the route seam is accepted.
- Response:
  freeze one summary-only JSON response posture over released kernel facts.
- Closeout Evidence:
  `OdeuRunSummary`, committed `v51b` response fixtures, and the route tests under
  `apps/api/tests/test_odeu_sim_vnext_plus125.py`.

### Edge 4: Invalid-Request Drift

- Risk:
  unsupported scenario names, invalid step counts, or forbidden override fields could
  be silently repaired instead of failing closed.
- Response:
  keep typed invalid-request posture explicit, require non-negative seeds, and forbid
  scenario overrides.
- Closeout Evidence:
  `OdeuRunRequestArtifact` strict validation,
  `test_build_odeu_run_response_fails_closed_on_negative_seed`, and
  `test_odeu_run_route_returns_typed_invalid_request_artifact`.

### Edge 5: Projection-Law Drift

- Risk:
  the route could emit a different `lane_summary`, a truncated metric object, or a
  zero-filled action vocabulary even while claiming to stay subordinate to the kernel.
- Response:
  freeze the response projection law: full released metric payload, exact three-key
  lane summary, and sparse observed-only action counts.
- Closeout Evidence:
  `OdeuRunSummary._validate_projection()`, `OdeuRunLaneSummary`,
  `current_metric: MetricPoint`, and the committed healthy/weak scenario fixtures.

### Edge 6: Kernel-Stack Compatibility Drift

- Risk:
  the route could run against an unexpected kernel contract or silently absorb later
  kernel drift without one typed mismatch carrier.
- Response:
  carry one explicit kernel-contract ref in the response and fail closed on mismatch.
- Closeout Evidence:
  `kernel_contract_ref = V51A_KERNEL_CONTRACT_REF`,
  `FAILURE_CODE_KERNEL_MISMATCH`, and
  `test_build_odeu_run_response_fails_closed_on_kernel_projection_mismatch`.

### Edge 7: Deterministic Replay Drift

- Risk:
  identical route requests could produce different JSON ordering or summary payloads
  even when the released kernel remains deterministic.
- Response:
  freeze deterministic request/response hashing and committed replay fixtures over the
  admitted starter scenarios.
- Closeout Evidence:
  `compute_odeu_run_request_hash(...)`, `compute_odeu_run_response_hash(...)`, and the
  committed `v51b` fixture set.

### Edge 8: Packaging / CI Drift

- Risk:
  the bounded route could pass targeted local tests but fail full-suite CI because the
  `apps/api` environment does not actually depend on the released kernel package.
- Response:
  keep `apps/api` package metadata and repo bootstrap aligned with the released
  `adeu-odeu-sim` dependency.
- Closeout Evidence:
  `apps/api/pyproject.toml`, the merged green `python` CI lane on PR `#347`, and the
  local `make check` pass that preceded merge.

### Edge 9: Main-Router Guard Drift

- Risk:
  the bounded route registration could be blocked by an outdated anti-coupling guard
  and tempt a broader guard relaxation than this slice needs.
- Response:
  admit only the narrow `V51-B` `main.py` router-registration seam and keep the
  storage boundary deferred.
- Closeout Evidence:
  `apps/api/tests/test_worker_governance_j2_guards_vnext_plus36.py` and the merged
  green `python` CI lane.

### Edge 10: Product-Surface Creep

- Risk:
  browser/UI work, persistent storage, or broader product routing could leak into the
  first API slice and blur family ownership.
- Response:
  keep `V51-B` bounded to one route module, targeted tests, and deterministic
  fixtures only.
- Closeout Evidence:
  shipped scope limited to `apps/api/src/adeu_api/odeu_sim.py`,
  `apps/api/src/adeu_api/main.py`, targeted tests/fixtures, package metadata, and
  closeout artifacts only.

### Edge 11: Prototype API Precedent Laundering

- Risk:
  the imported prototype `api.py` could be copied into live paths wholesale and treat
  prototype choices as released authority.
- Response:
  re-author the route in repo-native `apps/api` paths and keep the prototype API as
  shaping evidence only.
- Closeout Evidence:
  shipped route code exists only under `apps/api/src/adeu_api/`, while the imported
  bundle remains under `examples/external_prototypes/odeu-sandbox-app`.

## Current Judgment

- `V51-B` was the right second C-track move because it exposed the released kernel
  through one narrow stateless consumer without reopening kernel semantics in route
  code.
- the shipped result is properly bounded: one `POST /odeu-sim/run` route, released
  starter scenarios only, non-negative seed and bounded step validation, full released
  metric payload, exact three-key lane summary, sparse observed-only action counts,
  typed fail-closed invalid-request and kernel-mismatch responses, and no browser/UI
  or persistent state widening.
- review hardening materially improved the release: request validation is now
  centralized in typed route models, response projection mismatch fails closed through
  typed kernel-mismatch artifacts, `apps/api` explicitly depends on
  `adeu-odeu-sim`, and the main-router anti-coupling guard now admits this bounded
  consumer seam without reopening `storage.py`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-B` closed on
  `main` and the branch-local default next path advanced to `V51-C` / `vNext+126`.
