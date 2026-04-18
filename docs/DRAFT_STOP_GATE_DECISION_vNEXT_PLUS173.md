# Draft Stop-Gate Decision vNext+173

Status: proposed gate for `V63-A`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS173.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V63-A` session / view / bounded response schema set validates and
  exports cleanly;
- the lane handoff from `V62-C` is explicit via `agentic_de_lane_drift_record@1`;
- the selected principal remains explicit:
  - `remote_operator` only
  - `external_assistant` not selected
  - `human_via_connector` not selected;
- the admitted remote session / surface identity remains explicit and fail-closed;
- the admitted remote session verdict family remains explicit and bounded;
- the starter slice remains read-mostly plus one tiny bounded response set only:
  - `acknowledge`
  - `approve`
  - `continue`
  - `pause`
  - `escalate`;
- bounded responses consume an explicit control basis ref or equivalent matched to
  the selected response kind rather than inventing a new command ontology;
- `acknowledge` remains notification/session posture only and may not mutate
  continuation, communication, or authority state by itself;
- richer typed command/control, structured answers, and inspect-rich controls remain
  deferred to `V63-B`;
- shipped `V60` continuation lineage remains the only accepted continuation basis;
- shipped `V61` governed communication lineage remains the only accepted
  communication basis;
- evidence basis remains explicit, replayable, and fail-closed on missing or
  inconsistent remote session / view / response basis;
- remote transport remains non-authorizing:
  - not witness
  - not bridge office
  - not connector law
  - not repo authority
  - not execute authority
  - not dispatch authority;
- one selected remote surface remains path-level and non-generalizing by default:
  - not broad remote-admin law
  - not all-device or all-surface law
  - not connector law
  - not repo/execute/dispatch law;
- the implementation remains bounded to existing repo-owned packages plus one thin
  starter runner and one bounded remote view projection only;
- tests cover:
  - remote session replay / fail-closed behavior
  - explicit `remote_operator` principal typing
  - explicit shipped `V60` / `V61` basis consumption
  - bounded response kinds only
  - selected response semantics consume shipped law
  - no richer command bridge or structured answers in this slice
  - non-generalization and no repo / execute / dispatch drift

## Do Not Accept If

- `V63-A` silently reopens continuation law, communication law, connector law, or
  repo authority;
- remote presence or UI reachability is treated as admission or standing authority
  by itself;
- bounded responses are treated as a new independent command ontology;
- structured answers, inspect-rich controls, or richer command bridge semantics are
  pulled into the starter slice;
- one selected remote surface is over-read as broad remote-admin law, all-device
  law, repo authority, execute authority, or dispatch authority;
- the implementation invents free-form phone shell / terminal control or direct
  file-editing UI instead of consuming shipped governance surfaces first.

## Local Gate

- run `make arc-start-check ARC=173`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
