# Draft Stop-Gate Decision vNext+175

Status: proposed gate for `V63-C`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS175.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V63-C` advisory hardening schema validates and exports cleanly;
- the lane handoff from closed `V63-B` is explicit via
  `agentic_de_lane_drift_record@1`;
- the selected principal remains explicit:
  - `remote_operator` only
  - `external_assistant` not selected
  - `human_via_connector` not selected;
- the admitted remote session basis remains the shipped `V63-A` session only;
- the admitted remote view basis remains the shipped `V63-A` view only;
- the consumed richer intervention basis remains the shipped `V63-B`
  control-bridge lineage only;
- the consumed shipped `V63-A` starter-response lineage remains explicit where
  selected;
- the advisory evidence basis carries an explicit selected response/control kind
  summary where upstream response or control basis participates;
- hardening recommendation consumes explicit shipped basis rather than inventing
  a new remote command sovereign;
- committed lane artifacts outrank narrative interpretation or review prose when
  the advisory register derives evidence basis;
- evidence basis remains distinct from recommendation outcome;
- one explicit frozen-policy anchor remains required for replayability;
- hardening recommendation remains extensional, replayable, and fail-closed on
  missing or inconsistent basis;
- if both optional upstream response and control-bridge refs are `none`, the
  register may not overread richer intervention evidence;
- if optional upstream response or control-bridge basis is present, it must match
  the selected remote principal/session/surface posture;
- candidate outcomes remain advisory-only, non-entitling, and non-escalating by
  themselves:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_remote_operator_hardening`
  - `candidate_for_later_remote_surface_migration`
  - `not_selected_for_escalation`;
- shipped `V60` continuation lineage remains the only accepted continuation
  basis;
- shipped `V61` governed communication lineage remains the only accepted
  communication basis;
- advisory outputs remain non-generalizing by default:
  - not connector law
  - not `external_assistant` law
  - not `human_via_connector` law
  - not broader human-principal or multi-principal remote law
  - not broad remote-admin law
  - not all-device or all-surface law
  - not repo authority
  - not execute authority
  - not dispatch authority;
- the implementation remains bounded to existing repo-owned packages plus one
  thin advisory runner only;
- tests cover:
  - explicit shipped `V63-A` session/view basis consumption
  - explicit shipped `V63-B` control-bridge basis consumption
  - explicit selected response/control kind summary where relevant
  - explicit evidence-vs-recommendation separation
  - replay / fail-closed advisory behavior
  - no connector / remote-admin / repo / execute / dispatch drift

## Do Not Accept If

- `V63-C` silently reopens session admission, remote view, starter-response, or
  richer control-bridge law already closed in `V63-A` / `V63-B`;
- the advisory layer is over-read as remote authority, broad remote-admin law, or
  all-device law;
- response or control packets are treated as live entitlement or mutation
  channels under advisory cover;
- the advisory register admits repo authority, execute authority, or dispatch
  authority;
- `V63-C` is used to smuggle connector mutation or cross-principal law into the
  remote operator family;
- the hardening register invents a discretionary recommendation regime instead of
  consuming shipped basis and one frozen policy anchor.

## Local Gate

- run `make arc-start-check ARC=175`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
