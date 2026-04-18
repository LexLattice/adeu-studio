# Assessment vNext+173 Edges

Status: pre-lock edge assessment for `V63-A`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS173_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Remote Presence Could Quietly Become Standing Authority

- Risk:
  one phone-accessible or remote-accessible surface could be over-read as if remote
  reachability already grants office, authority, or standing permission.
- Response:
  keep remote session admission explicit, typed, and fail-closed.
  - presence is not permission
  - UI reachability is not admission
  - admitted remote session identity stays explicit

### Edge 2: Bounded Responses Could Invent A New Command Ontology

- Risk:
  the starter slice could treat `approve`, `continue`, `pause`, or `escalate` as if
  `V63-A` owns a new command language rather than consuming shipped law.
  The response record could also mis-name its consumed basis in a way that squeezes
  `acknowledge` or `escalate` into an approval/continuation-only slot.
- Response:
  keep starter responses downstream-consumption-only.
  - response basis stays typed as one explicit control basis ref or equivalent
    matched to the selected response kind
  - `approve` consumes shipped URM approval/session law
  - `continue` / `pause` consume shipped `V60` posture
  - `escalate` consumes shipped `V60` / `V61` posture
  - no new independent command ontology

### Edge 3: “Message Ingress” Could Quietly Swallow `V63-B`

- Risk:
  the starter slice could blur into a half-built command bridge by allowing richer
  message ingress than the bounded response set.
- Response:
  keep ingress in `V63-A` tiny and explicit.
  - acknowledgement or explicit bounded responses only
  - no structured answers or clarifications
  - no inspect-rich controls
  - richer command/control bridge deferred to `V63-B`

### Edge 4: Remote Principal Could Blur With Connector Principals

- Risk:
  the remote operator surface could drift into `external_assistant` or
  `human_via_connector` semantics once multiple access surfaces coexist.
- Response:
  keep principal typing explicit and singular in this slice.
  - `remote_operator` selected
  - connector-carried principals not selected here

### Edge 5: Remote Acknowledgement Could Be Over-Read As Witness Or Office

- Risk:
  one acknowledgement or bounded remote response could be treated as witness,
  bridge-office promotion, or connector law.
- Response:
  keep response artifacts transport-bounded and non-sovereign.
  - `acknowledge` is notification/session posture only and may not mutate
    continuation, communication, or authority state by itself
  - not witness
  - not bridge office
  - not connector law

### Edge 6: One Remote Surface Could Be Over-Read As Broad Remote-Admin Law

- Risk:
  one admitted remote operator surface could be treated as broad remote-admin law or
  all-device control law.
- Response:
  keep the starter path exact and non-generalizing by default.
  - one selected remote surface only
  - not broad remote-admin law
  - not all-device or all-surface law

### Edge 7: Remote Visibility Could Quietly Swallow Repo / Execute / Dispatch Law

- Risk:
  status and control visibility over a continuity-bound local-write exemplar could
  be over-read as repo authority, execute authority, or dispatch authority.
- Response:
  keep `V63-A` session/view/response only.
  - not repo authority
  - not execute authority
  - not dispatch authority
  - downstream exemplar remains consumed context only

### Edge 8: Workbench Or UI Doctrine Could Become A Hidden Sovereign

- Risk:
  because current workbench doctrine shapes the remote surface, UI convention could
  quietly replace explicit policy or packet law.
- Response:
  keep workbench doctrine shaping-only and subordinate to typed artifacts.
  - explicit frozen policy required
  - shipped lane artifacts and typed basis remain authoritative
  - UI doctrine may shape but not mint authority

## Current Judgment

- `V63-A` is the right next slice because the repo already has shipped continuation,
  governed communication, and connector families, but still lacks one bounded
  remote operator session/view starter over that same governed core.
- the follow-on should stay properly bounded:
  - one admitted remote surface only
  - one selected `remote_operator` principal only
  - one read-mostly view packet only
  - one tiny bounded response set only
  - shipped `V60` / `V61` lineage consumed intact
  - no connector mutation
  - no richer command/control bridge yet
  - no repo / execute / dispatch widening
- the next move after this starter slice, if `V63-A` lands cleanly, should be
  `V63-B` rather than widening `V63-A` in place.
