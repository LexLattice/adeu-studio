# Draft Stop-Gate Decision vNext+171

Status: proposed gate for `V62-B`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS171.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V62-B` schema validates and exports cleanly;
- the lane handoff from `V62-A` is explicit via `agentic_de_lane_drift_record@1`;
- the follow-on remains bound to the same exact admitted connector path only:
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
  - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
  - `provider = codex`
  - `execution_mode = live`
- the selected connector-carried principal remains explicit:
  - `external_assistant` only
- shipped `V62-A` admission and ingress bridge remain the only admitted connector
  basis;
- the egress bridge remains typed, replayable, and fail-closed on missing or
  inconsistent connector / egress / office / rewitness basis;
- `V61-B` bridge-office and rewitness posture is consumed explicitly where
  selected;
- positive rewitness consumption requires witness basis ref or certificate ref;
- direct consumed rewitness basis summary is carried when positive;
- `none` for optional bridge-office / rewitness refs means not selected and not
  consumed in that packet;
- optional office / rewitness refs are never inferred from prior emission
  capability or connector availability;
- latest continuation basis selection remains explicit and replayable;
- human-via-connector semantics remain absent from the shipped slice;
- raw outbound connector payload does not become native witness, charter
  amendment, continuation mutation, bridge office, repo authority, or execute
  authority;
- deterministic reference fixtures compile into the same egress bridge payload on
  repeated runs;
- the implementation remains bounded to existing repo-owned packages plus one thin
  runner seam over the selected backend routes;
- Python tests cover:
  - egress bridge replay / fail-closed behavior
  - explicit `V62-A` basis consumption
  - explicit `V61-B` basis consumption where selected
  - missing positive rewitness basis rejection
  - external-assistant principal typing
  - non-generalization and no-human-via-connector drift

## Do Not Accept If

- `V62-B` silently reopens connector admission law or ingress bridge law;
- outbound bridge is treated as bridge-office authority by itself;
- rewitness posture is treated as outbound authority without explicit basis;
- positive rewitness is cited without direct consumed basis summary;
- missing optional office / rewitness refs are treated as implicit selection from
  availability or prior capability;
- raw outbound connector payload is interpreted as native witness, charter
  amendment, continuation mutation, or execution authority;
- `V62-B` selects human-via-connector semantics without an explicit later lock;
- connector hardening, remote-operator, repo, execute, or dispatch widening lands
  in the slice;
- the implementation invents new connector product routes or UI semantics instead
  of consuming the shipped admitted connector path first.

## Local Gate

- run `make arc-start-check ARC=171`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
