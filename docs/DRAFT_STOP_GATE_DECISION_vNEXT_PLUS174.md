# Draft Stop-Gate Decision vNext+174

Status: proposed gate for `V63-B`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS174.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V63-B` richer control-bridge schema validates and exports cleanly;
- the lane handoff from closed `V63-A` is explicit via `agentic_de_lane_drift_record@1`;
- the selected principal remains explicit:
  - `remote_operator` only
  - `external_assistant` not selected
  - `human_via_connector` not selected;
- the admitted remote session basis remains the shipped `V63-A` session only;
- the admitted read-mostly view basis remains the shipped `V63-A` view only;
- richer intervention kinds remain bounded:
  - `structured_answer`
  - `clarification`
  - `inspect_rich`;
- richer intervention consumes explicit shipped basis rather than inventing a new
  sovereign command plane;
- richer intervention packets remain transport-bounded and non-mutating by
  themselves:
  - not charter mutation
  - not residual mutation
  - not continuation mutation
  - not communication-law mutation
  - not bridge office
  - not act authority;
- starter response law remains closed in `V63-A`;
- shipped `V60` continuation lineage remains the only accepted continuation basis;
- shipped `V61` governed communication lineage remains the only accepted
  communication basis;
- bridge basis remains explicit, replayable, and fail-closed on missing or
  inconsistent control basis;
- consumed shipped `V63-A` view basis remains explicit in the bridge record rather
  than hidden inside a generic control-basis slot;
- richer bridge outputs remain non-generalizing by default:
  - not connector law
  - not broad remote-admin law
  - not all-device or all-surface law
  - not repo authority
  - not execute authority
  - not dispatch authority;
- the implementation remains bounded to existing repo-owned packages plus one thin
  bridge runner only;
- tests cover:
  - explicit shipped `V63-A` session/view basis consumption
  - bounded richer intervention kinds only
  - replay / fail-closed bridge behavior
  - no repo / execute / dispatch drift
  - no connector-law drift

## Do Not Accept If

- `V63-B` silently reopens remote session admission already closed in `V63-A`;
- richer intervention is over-read as broad remote-admin or hidden office law;
- richer intervention is used as an implicit charter, residual, continuation, or
  communication-law mutation channel;
- the bridge admits free-form shell control, direct file editing, repo authority,
  execute authority, or dispatch authority;
- `V63-B` is used to smuggle connector mutation or external-assistant law into the
  remote operator family;
- the bridge invents an unconstrained command ontology instead of consuming shipped
  basis and explicit intervention kinds.

## Local Gate

- run `make arc-start-check ARC=174`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
