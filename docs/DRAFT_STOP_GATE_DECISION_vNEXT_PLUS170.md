# Draft Stop-Gate Decision vNext+170

Status: proposed gate for `V62-A`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS170.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V62-A` schemas validate and export cleanly;
- the lane handoff from `V61-C` is explicit via `agentic_de_lane_drift_record@1`;
- the starter path remains one exact connector path only:
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
  - `provider = codex`
  - `execution_mode = live`
- connector admission remains typed, replayable, and fail-closed on missing or stale
  snapshot / exposure / freshness basis;
- the connector admission verdict remains drawn only from the explicit starter verdict
  family;
- the selected connector-carried principal remains explicit:
  - `external_assistant` only
- human-via-connector semantics remain absent from the shipped slice;
- provenance fields remain explicit on both starter surfaces;
- the ingress bridge remains typed and replayable over shipped `V61-A`
  communication law only;
- raw connector payload does not become native witness, charter compilation,
  continuation mutation, bridge office, or act authority;
- deterministic reference fixtures compile into the same connector admission and
  ingress bridge payloads on repeated runs;
- the implementation remains bounded to existing repo-owned packages plus one thin
  runner seam over the selected backend routes;
- Python tests cover:
  - connector admission replay / fail-closed behavior
  - external-assistant principal typing
  - rejection of stale or missing connector basis
  - ingress bridge replay and boundedness
  - non-generalization and no-human-via-connector drift

## Do Not Accept If

- the starter path quietly becomes bidirectional bridge law;
- connector exposure or connector availability is treated as admission by itself;
- raw connector payload is interpreted as native witness, charter amendment, or act
  authority;
- `V62-A` silently reopens `V61` communication law or `V60` continuation law;
- `V62-A` silently depends on `V61-B` bridge-office or rewitness posture as a live
  ingress basis;
- `V62-A` selects human-via-connector semantics without an explicit later lock;
- replay, remote-operator, repo, execute, or dispatch widening lands in the slice;
- the implementation invents new connector product routes or UI semantics instead of
  retrofitting the existing snapshot / exposure seams first.

## Local Gate

- run `make arc-start-check ARC=170`
- full Python lane is intentionally skipped at starter-draft time because this bundle
  is docs-only
