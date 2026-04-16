# Draft Stop-Gate Decision vNext+167

Status: proposed gate for `V61-A`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS167.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new starter communication schemas validate and export cleanly;
- the committed reference ingress, descriptor, interpretation, and egress payloads
  replay deterministically for the same selected ingress basis and frozen policy;
- the starter path is frozen to the existing resident `/urm/copilot/send` seam with
  `copilot.user_message` only;
- the starter artifacts carry explicit:
  - source principal class
  - speaker class
  - surface instance or session identity
- the surface-authority descriptor remains surface-affordance / bounded-authority
  posture only and does not interpret message meaning by itself;
- ingress interpretation remains explicit and replayable and does not mutate charter,
  residual, or continuation state;
- `charter_amendment_candidate` remains posture-only and non-mutating in this slice;
- egress remains typed communication posture only and does not mint act authority,
  repo-write authority, or native witness;
- resident runtime emission remains distinct from explicit bridge-office behavior;
- Python tests cover:
  - schema/model validation,
  - deterministic replayability of ingress/descriptor/interpretation/egress,
  - fail-closed starter seam selection,
  - non-mutating interpretation posture,
  - thin CLI and resident send-path retrofit behavior.

## Do Not Accept If

- raw transcript or generic chat memory is treated as governed communication law;
- UI send access is treated as if it were already bridge-office binding;
- `V61-A` reopens `V60` seed-ingress, charter, residual, or continuation law;
- message interpretation silently mutates charter, residual, or continuation state;
- the starter slice widens beyond the existing resident send seam into connector,
  remote-operator, repo-authority, replay, execute, or dispatch law;
- communication packets are treated as native witness or act authority by default;
- web copilot or desktop workbench are implemented as separate starter seams instead
  of consumers of the same backend seam;
- bridge-office binding or rewitness lands in `V61-A`.

## Local Gate

- run `make arc-start-check ARC=167`
- full Python lane may remain skipped while the diff is docs-only
