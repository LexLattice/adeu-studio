# Draft Stop-Gate Decision vNext+178

Status: proposed gate for `V64-C`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS178.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V64-C` advisory hardening schema validates and exports cleanly;
- the lane handoff from closed `V64-B` is explicit via
  `agentic_de_lane_drift_record@1`;
- the consumed writable-surface basis remains explicit:
  - shipped `V64-A` descriptor only
  - shipped `V64-A` lease only
  - shipped `V64-A` surface admission only;
- the consumed restoration basis remains explicit:
  - shipped `V64-B` restoration only where relevant
  - shipped `V64-B` reintegration only where relevant;
- the selected advisory scope remains explicit:
  - same selected writable surface only
  - same exact admitted target only
  - not fresh surface selection
  - not fresh lease issuance
  - not fresh target admission
  - not restoration or reintegration mutation;
- evidence basis remains distinct from recommendation;
- committed lane artifacts outrank narrative interpretation when the advisory
  register derives its basis;
- explicit frozen-policy anchoring and replayability remain first-class:
  - same shipped basis plus same frozen policy yields the same recommendation;
- optional upstream restoration / reintegration basis remains fail-closed:
  - if both refs are `none`, no restoration-local overread
  - restoration ref may appear alone only for restoration-local evidence
  - reintegration ref may not appear without restoration ref
  - co-present refs must remain one shipped restoration chain
  - if present, they must match selected writable-surface and target posture;
- preserved write-semantics summary remains explicit in the advisory evidence basis:
  - no append / overwrite / rename / delete overread;
- consumed basis remains explicit:
  - shipped `V59` continuity lineage only
  - shipped `V60` continuation lineage only
  - shipped `V61` communication lineage only where relevant;
- advisory outcomes remain non-entitling and non-escalating by themselves;
- the implementation remains bounded to existing repo-owned packages plus one thin
  advisory runner only;
- outputs remain non-equivalent to:
  - all-repo authority
  - broad repo-admin law
  - shell authority
  - execute authority
  - dispatch authority
  - delegated worker authority
  - connector law
  - remote-operator law;
- tests cover:
  - same-lineage preservation
  - fail-closed advisory basis validation
  - evidence-vs-recommendation separation
  - optional upstream restoration / reintegration consistency
  - no all-repo / shell / execute / dispatch / worker drift

## Do Not Accept If

- `V64-C` reopens writable-surface selection, lease issuance, or target admission
  in place;
- advisory hardening is treated as live restoration or live repo authority;
- restoration or reintegration lineage is overread when absent or mismatched;
- reintegration lineage is carried without restoration lineage;
- non-selected write semantics are overread from restoration-local evidence;
- narrative review or prose is allowed to outrank committed lane artifacts;
- one writable-surface exemplar is used to smuggle all-repo, shell, execute,
  dispatch, or worker authority into the family.

## Local Gate

- run `make arc-start-check ARC=178`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
