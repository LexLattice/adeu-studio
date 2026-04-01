# Draft Stop-Gate Decision vNext+104

Status: proposed gate for `V45-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS104.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo releases one canonical `repo_optimization_register@1` with authoritative and
  mirrored schema parity;
- the register binds to one explicit repo snapshot and one explicit bounded source set
  with source-set hash, extraction posture, and extraction method;
- the register binds consistently to released `V45-A` through `V45-D` descriptive
  artifacts over the same snapshot identity with explicit artifact-local
  source-scope compatibility;
- each optimization row preserves explicit distinction between:
  - descriptive finding;
  - optimization candidate;
  - amendment entitlement;
- each optimization row carries explicit compression axis, optimization posture,
  support basis, priority posture, derivation posture/method, and source artifact refs;
- mixed findings remain representable through optional bounded secondary tags rather
  than forced flattening into one primary label only;
- any `cross_surface_cluster` row carries an explicit member carrier with resolvable
  member refs;
- `amendment_entitlement` is frozen to a non-authorizing starter posture;
- fail-closed laws reject unsupported optimization claims, malformed scope refs,
  missing support basis, source refs outside the declared source set, and authority
  laundering;
- scoped Python tests cover schema/model validation, deterministic fixture replay,
  cross-artifact binding, and fail-closed rejection.

## Do Not Accept If

- the register turns hotspot or consolidation signals into mutation or scheduling
  entitlement;
- optimization rows rely on file size or vague prose only without explicit support
  basis;
- cross-artifact binding to released `V45-A` through `V45-D` surfaces is missing or
  snapshot-inconsistent or source-scope-incompatible;
- `cross_surface_cluster` appears without an explicit member carrier;
- `source_artifact_refs` are not source-set-membership checked;
- the slice widens into `V45-F`, recursive governance, or automatic repo mutation.

## Local Gate

- run targeted repo-description checks for the changed Python surface once
  implementation begins;
- while the bundle is docs-only, run `make arc-start-check ARC=104`.
