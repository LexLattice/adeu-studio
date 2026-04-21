# Draft Stop-Gate Decision vNext+182

Status: proposed gate for `V66-A`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS182.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V66-A` ANM-native starter schemas validate and export cleanly;
- the consumed `V47` basis remains explicit:
  - released `V47-A` through `V47-F` ANM substrate only;
- the starter source-set boundary remains explicit:
  - `discovered_doc_inventory`
  - `governed_anm_source_set`
  - the governed ANM source set is not silently widened to the whole repo;
- starter classification axes remain explicit and non-collapsed:
  - `doc_class`
  - `authority_layer`
  - `source_posture`
  - `lifecycle_status`
  - `classification_status`;
- the selected starter outputs remain bounded:
  - `anm_source_set_manifest@1`
  - `anm_doc_authority_profile@1`
  - `anm_doc_class_policy@1`
  - no generated reader projection yet
  - no semantic diff report yet
  - no full migration binding profile yet
  - no stable compile report artifact yet;
- minimal companion registration remains explicit and fail-closed:
  - unregistered companions fail closed
  - contradictory host / companion linkage fails closed
  - supersession claims without explicit transition law fail closed;
- plain support / historical markdown does not become hard-gated starter ANM
  source merely because it exists;
- document-class policy remains explicit:
  - lock
  - architecture
  - planning
  - support
  - non-governance;
- outputs remain non-equivalent to:
  - implementation authority
  - runtime behavior by itself
  - markdown supersession by itself
  - generated-reader authority by itself;
- the implementation remains bounded to existing repo-owned ANM packages only;
- tests cover:
  - source-set boundary separation
  - explicit axis separation
  - companion registration failure posture
  - class-policy overpromotion rejection
  - no `V47` language widening
  - no `V66-B` / `V66-C` surfaces landing early.

## Do Not Accept If

- `V66-A` collapses doc class, authority layer, source posture, lifecycle, and
  classification into one flat doc-type axis;
- the starter slice treats all markdown in the repo as governed ANM source by
  default;
- companion posture is accepted without explicit registration;
- markdown supersession is permitted without explicit transition law;
- generated reader-view or semantic-diff surfaces are smuggled into the starter
  slice as if they were already selected;
- a stable compile-report artifact is minted in place of the deferred `V66-C`
  advisory lane;
- review prose or front matter is allowed to mint obligations by implication;
- support-layer ANM posture is allowed to overpromote into lock or planning law.

## Local Gate

- run `make arc-start-check ARC=182`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only

