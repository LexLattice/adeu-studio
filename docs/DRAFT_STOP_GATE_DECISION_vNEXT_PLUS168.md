# Draft Stop-Gate Decision vNext+168

Status: proposed gate for `V61-B`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS168.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new bridge-office binding and rewitness schemas validate and export cleanly;
- the committed reference bridge-binding and rewitness payloads replay deterministically
  for the same selected communication lineage and frozen policy;
- the slice remains frozen to the existing resident `/urm/copilot/send` seam with
  `copilot.user_message` only;
- bridge-office binding remains explicit, replayable, and fail-closed:
  - same bridge facts
  - same latest communication lineage
  - same frozen policy
  - same office posture
- communication access or prior resident emission capability does not become ambient
  bridge office;
- rewitness remains explicit, replayable, and fail-closed:
  - raw communication remains non-native witness by default
  - raw transcript remains non-native witness by default
  - ambiguity blocks promotion
- positive rewitness remains bounded to explicit witness-candidate posture only and
  does not mint native witness, reintegration closure, act authority, or repo-write
  authority;
- Python tests cover:
  - schema/model validation,
  - deterministic replayability of bridge binding and rewitness,
  - fail-closed seam selection,
  - non-generalization and non-authority posture,
  - thin CLI and backend seam behavior.

## Do Not Accept If

- communication access is treated as if it were already bridge office;
- rewitness silently promotes transcript or generic chat memory into native witness;
- `V61-B` reopens `V60` charter, residual, or continuation law;
- the slice widens beyond the existing resident seam into connector, remote-operator,
  repo-authority, replay, execute, or dispatch law;
- office binding or rewitness is treated as act authority or repo-write authority;
- evidence from the selected seam is over-read into broader connector, remote, or
  execution law.

## Local Gate

- run `make arc-start-check ARC=168`
- full Python lane may remain skipped while the diff is docs-only
