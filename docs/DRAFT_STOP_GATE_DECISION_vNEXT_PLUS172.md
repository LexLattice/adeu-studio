# Draft Stop-Gate Decision vNext+172

Status: proposed gate for `V62-C`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS172.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V62-C` schema validates and exports cleanly;
- the lane handoff from `V62-B` is explicit via `agentic_de_lane_drift_record@1`;
- the advisory register remains bound to the same exact admitted connector path
  only:
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
  - `provider = codex`
  - `execution_mode = live`
- the selected connector-carried principal remains explicit:
  - `external_assistant` only;
- shipped `V62-A` connector admission and ingress bridge remain the only admitted
  connector basis;
- shipped `V62-B` egress bridge remains the only accepted outbound bridge basis;
- evidence basis remains distinct from recommendation outcome;
- committed lane artifacts outrank narrative interpretation when the advisory
  register is derived;
- recommendation remains typed, replayable, and fail-closed on missing or
  inconsistent connector / communication / bridge-office / rewitness basis;
- explicit frozen-policy anchor remains required for replayability;
- positive rewitness basis or certificate posture is carried explicitly where
  relevant;
- positive rewitness basis/certificate posture remains consistent with the actual
  selected upstream rewitness posture and fails closed otherwise;
- `keep_warning_only` retains current advisory posture only;
- latest continuation basis selection remains explicit and replayable;
- candidate outcomes remain non-entitling and non-escalating by themselves;
- later connector-hardening or connector-migration scope remains unspecified unless
  a later lock selects it explicitly;
- human-via-connector semantics remain absent from the shipped slice;
- the advisory register does not become connector admission, bridge office,
  rewitness, repo authority, execute authority, or dispatch authority;
- deterministic reference fixtures compile into the same advisory output on
  repeated runs;
- the implementation remains bounded to existing repo-owned packages plus one thin
  runner seam over the selected backend routes;
- Python tests cover:
  - recommendation replay / fail-closed behavior
  - explicit `V62-A` / `V62-B` basis consumption
  - evidence-vs-recommendation separation
  - explicit positive rewitness basis posture where relevant
  - external-assistant principal typing
  - non-generalization and no-human-via-connector drift

## Do Not Accept If

- `V62-C` silently reopens connector admission law or bridge law;
- advisory output is treated as connector permission, bridge office, rewitness, or
  human-via-connector selection by itself;
- artifact refs replace shipped verdicts or explicit basis posture;
- candidate labels are treated as implied authorization or migration scope;
- one connector exemplar is over-read as broader fleet trust, remote-operator law,
  bridge-office-family law, rewitness-family law, repo authority, execute
  authority, or dispatch authority;
- the slice imports connector-fleet widening, human-via-connector semantics,
  remote-operator UX, repo authority, execute authority, or dispatch authority;
- the implementation invents new connector product routes or UI semantics instead
  of consuming the shipped admitted connector path first.

## Local Gate

- run `make arc-start-check ARC=172`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
