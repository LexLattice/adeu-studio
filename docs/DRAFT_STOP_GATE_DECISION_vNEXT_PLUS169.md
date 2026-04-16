# Draft Stop-Gate Decision vNext+169

Status: proposed gate for `V61-C`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS169.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new governed communication hardening schema validates and exports cleanly;
- the committed hardening payload replays deterministically for the same selected
  communication lineage and frozen policy;
- the slice remains frozen to the existing resident `/urm/copilot/send` seam with
  `copilot.user_message` only and the same shipped `V61-A` / `V61-B` lineage;
- recommendation remains extensional, replayable, and evidence-first:
  - same selected evidence chain
  - same frozen policy
  - same recommendation
- positive rewitness may not be over-read from outcome alone:
  - explicit witness basis ref or certificate ref is carried when present
  - latest continuation basis selection remains explicit, not ambient
- evidence basis remains distinct from recommendation;
- lineage-root non-independence remains explicit and deduplicated;
- communication exemplar evidence remains non-generalizing by default:
  - not connector-family law
  - not remote-operator law
  - not bridge-office-family law
  - not rewitness-family law
  - not repo/execute authority law
- outputs remain advisory-only and non-entitling:
  - no live behavior mutation
  - no communication packet mutation
  - no bridge-office or rewitness mutation
  - no advisory-to-live promotion
  - later communication-hardening scope remains unspecified without a later lock
  - later bridge-office / rewitness migration scope remains unspecified without a
    later lock
- Python tests cover:
  - schema/model validation,
  - deterministic replayability of the advisory result,
  - fail-closed seam selection,
  - explicit evidence-vs-recommendation separation,
  - non-generalization and non-authority posture,
  - thin CLI and backend seam behavior.

## Do Not Accept If

- the hardening register can yield different recommendations for the same evidence
  chain and frozen policy;
- advisory output is treated as if it already mints bridge-office, rewitness,
  connector, remote, repo, or execute authority;
- `V61-C` reopens `V61-A` communication law or `V61-B` bridge/rewitness law;
- the slice widens beyond the existing resident seam into connector transport,
  remote-operator, repo-authority, execute, or dispatch law;
- evidence from the selected seam is over-read into broader family law by default.

## Local Gate

- run `make arc-start-check ARC=169`
- full Python lane may remain skipped while the diff is docs-only
