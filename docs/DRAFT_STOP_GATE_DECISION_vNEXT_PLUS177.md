# Draft Stop-Gate Decision vNext+177

Status: proposed gate for `V64-B`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS177.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V64-B` restoration / reintegration schemas validate and export cleanly;
- the lane handoff from closed `V64-A` is explicit via
  `agentic_de_lane_drift_record@1`;
- the consumed writable-surface basis remains explicit:
  - shipped `V64-A` descriptor only
  - shipped `V64-A` lease only
  - shipped `V64-A` surface admission only;
- the consumed concrete write-effect basis remains explicit:
  - shipped exact write-effect observation / conformance / admission lineage only;
- the selected restoration scope remains explicit:
  - same selected writable surface only
  - same exact admitted target only
  - not fresh surface selection
  - not fresh lease issuance
  - not fresh target admission;
- target carry-through remains explicit:
  - target membership basis remains first-class
  - target occupancy / admissibility basis remains first-class;
- restoration remains distinct from fresh writable entitlement minting;
- restoration remains distinct from fresh target admission minting;
- consumed basis remains explicit:
  - shipped `V59` continuity lineage only
  - shipped `V60` continuation lineage only
  - shipped `V61` communication lineage only where relevant;
- mutation semantics remain preserved from `V64-A`:
  - keep the narrow `local_write` / `create_new` posture only
  - do not widen append / overwrite / rename / delete semantics in `V64-B`;
- restoration remains replayable and fail-closed:
  - same shipped basis plus same exact target plus same frozen policy yields the
    same outputs
  - missing or inconsistent basis fails closed
  - non-admitted or out-of-surface targets fail closed;
- the implementation remains bounded to existing repo-owned packages plus one thin
  restoration runner only;
- outputs remain non-equivalent to:
  - all-repo authority
  - shell authority
  - execute authority
  - dispatch authority
  - delegated worker authority
  - connector law
  - remote-operator law;
- tests cover:
  - same-surface and same-target preservation
  - fail-closed restoration basis validation
  - restoration not minting fresh surface selection or fresh lease issuance
  - preserved narrow write semantics only
  - no all-repo / shell / execute / dispatch / worker drift

## Do Not Accept If

- `V64-B` reopens writable-surface selection or lease issuance in place;
- restoration is treated as blanket standing authority for other in-surface or
  out-of-surface targets;
- restoration is treated as fresh target admission merely because prior `V64-A`
  entitlement existed;
- restoration widens mutation semantics beyond the shipped `V64-A` posture;
- continuity, communication, connector, or remote-operator lineage is treated as
  fresh writable entitlement;
- `V64-B` is used to smuggle all-repo, shell, execute, dispatch, or worker
  authority into the family.

## Local Gate

- run `make arc-start-check ARC=177`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
